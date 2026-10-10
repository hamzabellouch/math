import OAI.Analysis.Laughlin.FourBody.Matrix

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix
def lower_8 : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 0, 0;
    0, 1, 0, 0;
    0, -1, 1, 0;
    0, 7/4, 0, 1]
def pivots_8 : Fin 4 → ℚ :=
  ![0, 38057801156652456127253649/187904819200000000000000, 0, 0]

end Laughlin.Certificate

end OAI
