import OAI.Geometry.RCD.Coordinates.MatrixNormConversion

namespace OAI

/-! # Bilinear forms determined by their finite coordinate entries -/

open scoped BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {m : ℕ} {F : Type*} [AddCommGroup F] [Module ℝ F]

def coordinateBilinear (a : Fin m → Fin m → F) :
    Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] F :=
  (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.constr ℝ fun i =>
    (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.constr ℝ (a i)

theorem coordinateBilinear_apply (a : Fin m → Fin m → F) (v w : Euclidean m) :
    coordinateBilinear a v w = ∑ i : Fin m, ∑ j : Fin m, (v i * w j) • a i j := by
  simp only [coordinateBilinear, Module.Basis.constr_apply_fintype,
    LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
  rfl

theorem coordinateBilinear_symmetric (a : Fin m → Fin m → F)
    (ha : ∀ i j, a i j = a j i) (v w : Euclidean m) :
    coordinateBilinear a v w = coordinateBilinear a w v := by
  rw [coordinateBilinear_apply, coordinateBilinear_apply, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [ha i j, mul_comm]

end RegularPointCoordinates

end

end OAI
