import Mathlib

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def f {R : Type*} [CommRing R] (z : R) : R := (105 + z * (122 + z * (125 + z * (132 + z * (109 + z * (42 + z * (48 + z * (77 + z * (78 + z * (119 + z * (136 + z * (31 + z * (34 + z * (130 + z * (58 + z * (89 + z * (116 + z * (0 + z * (102 + z * (128 + z * 1))))))))))))))))))))

def u0 {R : Type*} [CommRing R] (z : R) : R := (0 + z * 1)

theorem initial {R : Type*} [CommRing R] (z : R) : z ^ (139 ^ 0) = u0 z := by simp [u0]

end DimensionTen.Mod139

end

end OAI
