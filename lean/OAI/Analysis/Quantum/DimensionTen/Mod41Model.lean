import Mathlib

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41
def f {R : Type*} [CommRing R] (z : R) : R := (36 + z * (13 + z * (30 + z * (1 + z * (32 + z * (5 + z * (1 + z * (33 + z * (20 + z * (11 + z * (15 + z * (31 + z * (14 + z * (7 + z * (25 + z * (36 + z * (33 + z * (23 + z * (17 + z * (30 + z * 1))))))))))))))))))))

def u0 {R : Type*} [CommRing R] (z : R) : R := (0 + z * 1)

theorem initial {R : Type*} [CommRing R] (z : R) : z ^ (41 ^ 0) = u0 z := by simp [u0]

end DimensionTen.Mod41

end

end OAI
