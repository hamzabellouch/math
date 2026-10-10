import OAI.Analysis.Laughlin.FiniteFlux.Gram072

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix
theorem gram_7 : gramRational 7 =
  !![1440, 0, -360, 2520;
    0, 0, 0, 0;
    -360, 0, 90, -630;
    2520, 0, -630, 4410] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact gram_7_1_1
  · exact gram_7_1_3
  · exact gram_7_1_5
  · exact gram_7_1_7
  · exact gram_7_3_1
  · exact gram_7_3_3
  · exact gram_7_3_5
  · exact gram_7_3_7
  · exact gram_7_5_1
  · exact gram_7_5_3
  · exact gram_7_5_5
  · exact gram_7_5_7
  · exact gram_7_7_1
  · exact gram_7_7_3
  · exact gram_7_7_5
  · exact gram_7_7_7

end Laughlin.Certificate

end OAI
