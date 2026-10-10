import Mathlib

namespace OAI


noncomputable section

namespace Problem355.NormFoundation

open Matrix

def momentColumn {K : Type*} [CommRing K] (x : K) : Fin 3 → K :=
  ![1, x, x ^ 2]

def momentMatrix {K : Type*} [CommRing K] (x y z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 1, 1; x, y, z; x ^ 2, y ^ 2, z ^ 2]

theorem det_momentMatrix {K : Type*} [CommRing K] (x y z : K) :
    (momentMatrix x y z).det = (y - x) * (z - x) * (z - y) := by
  rw [Matrix.det_fin_three]
  simp [momentMatrix]
  ring

theorem det_momentMatrix_ne_zero {K : Type*} [CommRing K] [IsDomain K]
    {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (momentMatrix x y z).det ≠ 0 := by
  rw [det_momentMatrix]
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hxy.symm)
    (sub_ne_zero.mpr hxz.symm)) (sub_ne_zero.mpr hyz.symm)

theorem norm_det_momentMatrix_ne_zero {F K : Type*} [Field F] [Field K]
    [Algebra F K] [Module.Finite F K]
    {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Algebra.norm F (momentMatrix x y z).det ≠ 0 := by
  exact Algebra.norm_ne_zero_iff.mpr (det_momentMatrix_ne_zero hxy hxz hyz)

theorem norm_det_momentMatrix_eq_prod {F K : Type*} [Field F] [Field K]
    [Finite K] [Algebra F K] (x y z : K) :
    algebraMap F K (Algebra.norm F (momentMatrix x y z).det) =
      ∏ j ∈ Finset.range (Module.finrank F K),
        ((y - x) * (z - x) * (z - y)) ^ (Nat.card F ^ j) := by
  rw [FiniteField.algebraMap_norm_eq_prod_pow, det_momentMatrix]

end Problem355.NormFoundation

end

end OAI
