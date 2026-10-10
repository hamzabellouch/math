import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.NormalizedNormalCoordinates

namespace OAI

namespace RieszRectifiability

noncomputable section

open WithLp
open scoped NNReal

def normalDirection {q d : ℕ} (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q) : Ambient d :=
  N (EuclideanSpace.basisFun (Fin q) ℝ i)

def normalCoordinate {q d : ℕ} (a : Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (i : Fin q) (x : Ambient d) : ℝ := N.toContinuousLinearMap.adjoint (x - a) i

theorem normalDirection_norm {q d : ℕ} (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q) :
    ‖normalDirection N i‖ = 1 := by
  rw [normalDirection, N.norm_map]
  exact (EuclideanSpace.basisFun (Fin q) ℝ).norm_eq_one i

theorem normalCoordinate_eq_inner {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q) (x : Ambient d) :
    normalCoordinate a N i x = inner ℝ (normalDirection N i) (x - a) := by
  calc
    _ = inner ℝ (EuclideanSpace.basisFun (Fin q) ℝ i)
        (N.toContinuousLinearMap.adjoint (x - a)) :=
      (EuclideanSpace.basisFun_inner (Fin q) ℝ (N.toContinuousLinearMap.adjoint (x - a)) i).symm
    _ = _ := N.toContinuousLinearMap.adjoint_inner_right _ _

theorem normalCoordinate_difference {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q) (x y : Ambient d) :
    normalCoordinate a N i x - normalCoordinate a N i y = inner ℝ (normalDirection N i) (x - y) := by
  rw [normalCoordinate_eq_inner, normalCoordinate_eq_inner, ← inner_sub_right,
    sub_sub_sub_cancel_right]

theorem normalCoordinate_lipschitz {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q) : LipschitzWith 1 (normalCoordinate a N i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, normalCoordinate_difference, dist_eq_norm]
  have h := abs_real_inner_le_norm (normalDirection N i) (x - y)
  simpa only [normalDirection_norm, one_mul] using! h

theorem normalCoordinate_normalized_vector {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (δ : ℝ) (x : Ambient d) :
    toLp 2 (fun i => normalCoordinate a N i x / δ) = normalizedNormalHeight a N δ x := by
  ext i
  change (N.toContinuousLinearMap.adjoint (x - a) i) / δ =
    δ⁻¹ * (N.toContinuousLinearMap.adjoint (x - a) i)
  rw [div_eq_mul_inv, mul_comm]

end

end RieszRectifiability

end OAI
