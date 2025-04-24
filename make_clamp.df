method Clamp(x: int, lower: int, upper: int) returns (result: int)
  requires lower <= upper
  ensures lower <= result <= upper
  ensures (x < lower ==> result == lower)
  ensures (x > upper ==> result == upper)
  ensures (lower <= x <= upper ==> result == x)
{
  if x < lower {
    result := lower;
  } else if x > upper {
    result := upper;
  } else {
    result := x;
  }
}
