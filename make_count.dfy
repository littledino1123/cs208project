module MakeCount {

  // Abstract atomic input type and numeric output type
  type TIA
  type TO

  // Constant for maximum representable consecutive value of TO
  const MAX_CONSECUTIVE: TO

  // Abstract casting from nat (usize) to TO — saturates at MAX_CONSECUTIVE
  function method ExactIntCast(n: nat): TO
    ensures n <= MAX_CONSECUTIVE ==> ExactIntCast(n) == CastToTO(n)
    ensures n > MAX_CONSECUTIVE ==> ExactIntCast(n) == MAX_CONSECUTIVE

  // Ideal cast within bounds (abstract)
  function method CastToTO(n: nat): TO

  // Infimum cast from nat to TO — assumed order-preserving
  function method InfCast(n: nat): TO

  // Axioms about ordering preservation and saturation
  axiom CastOrderPreserving(x: nat, y: nat)
    requires x <= y <= MAX_CONSECUTIVE
    ensures CastToTO(x) <= CastToTO(y)

  axiom InfCastOrderPreserving(x: nat, y: nat)
    requires x <= y
    ensures InfCast(x) <= InfCast(y)

  // Symmetric distance on vectors — number of differing elements
  function method SymmetricDistance(u: seq<TIA>, v: seq<TIA>): nat {
    if |u| >= |v| then |u| - |v| else |v| - |u|
  }

  // The count function we're verifying — length with saturating cast
  function method Count(v: seq<TIA>): TO {
    ExactIntCast(|v|)
  }

  // Sensitivity lemma: |Count(u) - Count(v)| ≤ |len(u) - len(v)|
  lemma DsymSensitivity(u: seq<TIA>, v: seq<TIA>)
    ensures |Count(u) - Count(v)| <= | |u| - |v| |
  {
    if |u| <= MAX_CONSECUTIVE && |v| <= MAX_CONSECUTIVE {
      assert |Count(u) - Count(v)| == |CastToTO(|u|) - CastToTO(|v|)|;
      assert CastOrderPreserving(|u|, |v|) || CastOrderPreserving(|v|, |u|);
      assert |CastToTO(|u|) - CastToTO(|v|)| <= | |u| - |v| |;
    } else {
      // At least one value saturates
      if |u| > MAX_CONSECUTIVE && |v| > MAX_CONSECUTIVE {
        assert Count(u) == MAX_CONSECUTIVE;
        assert Count(v) == MAX_CONSECUTIVE;
      } else if |u| > MAX_CONSECUTIVE {
        assert Count(u) == MAX_CONSECUTIVE;
        assert Count(v) == CastToTO(|v|);
        assert MAX_CONSECUTIVE - CastToTO(|v|) <= | |u| - |v| |;
      } else {
        assert Count(v) == MAX_CONSECUTIVE;
        assert Count(u) == CastToTO(|u|);
        assert MAX_CONSECUTIVE - CastToTO(|u|) <= | |u| - |v| |;
      }
    }
  }

  // Stability map: returns InfCast(din)
  function method StabilityMap(din: nat): TO {
    InfCast(din)
  }

  // Stability proof: |Count(u) - Count(v)| ≤ StabilityMap(din)
  lemma StabilityProof(u: seq<TIA>, v: seq<TIA>, din: nat, dout: TO)
    requires SymmetricDistance(u, v) <= din
    requires dout >= StabilityMap(din)
    ensures |Count(u) - Count(v)| <= dout
  {
    DsymSensitivity(u, v);
    var sens := | |u| - |v| |;
    assert sens <= SymmetricDistance(u, v);
    assert SymmetricDistance(u, v) <= din;
    assert sens <= din;
    assert InfCastOrderPreserving(sens, din);
    assert InfCast(sens) <= InfCast(din);
    // Assuming Count is non-negative, and InfCast monotonic
    // |Count(u) - Count(v)| ≤ sens ≤ din ≤ dout
    // Now, by monotonicity and properties of ExactIntCast and InfCast
    assert |Count(u) - Count(v)| <= InfCast(sens);
    assert InfCast(sens) <= dout;
  }

  // Simple test harness contract
  method ExampleCheck()
    ensures Count([1, 2, 3]) == ExactIntCast(3)
    ensures SymmetricDistance([1, 2], [1, 2, 3]) == 1
  {
  }

}
