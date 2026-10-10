import Mathlib

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131
def f {R : Type*} [CommRing R] (z : R) : R := (50 + z * (47 + z * (64 + z * (23 + z * (71 + z * (114 + z * (2 + z * (70 + z * (100 + z * (54 + z * (17 + z * (116 + z * (85 + z * (77 + z * (7 + z * (37 + z * (86 + z * (49 + z * (59 + z * (66 + z * 1))))))))))))))))))))

def u0 {R : Type*} [CommRing R] (z : R) : R := (0 + z * 1)

theorem initial {R : Type*} [CommRing R] (z : R) : z ^ (131 ^ 0) = u0 z := by simp [u0]

end DimensionTen.Mod131

end

end OAI
