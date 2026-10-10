import Mathlib
import OAI.Analysis.FreeWords.FreeWordCore
import OAI.Analysis.FreeWords.OperatorRows

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators ComplexOrder InnerProductSpace

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {r d : ℕ}

namespace FreePartitions

variable (P : FreePartitions τ r d)

theorem creation_row (hτ : τ 1 = 1) (j : Fin r) :
    RowSqBound (fun a => creationOp τ P.S j (P.centered j a)) (d : ℝ)⁻¹ := by
  intro x
  let T := (tailSpace τ P.S j).starProjection
  have hn a : ‖T (x a)‖ ≤ ‖x a‖ :=
    (T.le_opNorm _).trans (by
      have hh := (tailSpace τ P.S j).starProjection_norm_le
      calc
        _ ≤ 1 * ‖x a‖ := mul_le_mul_of_nonneg_right hh (norm_nonneg _)
        _ = _ := one_mul _)
  change ‖∑ a, τ.gnsStarAlgHom (P.centered j a) (T (x a))‖ ^ 2 ≤ _
  rw [P.norm_create_row_sq hτ j (fun a => T (x a))
    (fun a => Submodule.starProjection_apply_mem _ _)]
  apply (sub_le_self _ (by positivity)).trans
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun a _ => pow_le_pow_left₀ (norm_nonneg _) (hn a) 2))
    (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem gns_projection (j : Fin r) (a : Fin d) :
    IsStarProjection (τ.gnsStarAlgHom (P.e j a)) := by
  constructor
  · change τ.gnsStarAlgHom (P.e j a) * τ.gnsStarAlgHom (P.e j a) = _
    rw [← map_mul, P.mul]
    simp
  · change star (τ.gnsStarAlgHom (P.e j a)) = _
    rw [← map_star, P.selfadjoint]

theorem gns_projection_orthogonal (j : Fin r) (a b : Fin d) (hab : a ≠ b) :
    τ.gnsStarAlgHom (P.e j a) * τ.gnsStarAlgHom (P.e j b) = 0 := by
  rw [← map_mul, P.mul, ite_eq_right hab, map_zero]

theorem gns_projection_sum (j : Fin r) :
    (∑ a, τ.gnsStarAlgHom (P.e j a)) = 1 := by
  rw [← map_sum, P.sum, map_one]

theorem preservation_eq_compress (j : Fin r) (a : Fin d) :
    preservationOp τ P.S j (P.centered j a) =
      (headSpace τ P.S j).starProjection *
        (τ.gnsStarAlgHom (P.e j a) - (d : ℂ)⁻¹ • 1) *
        (headSpace τ P.S j).starProjection := by
  simp only [preservationOp, centered, map_sub, map_smul, map_one]

end FreePartitions

end

end KKFreeWords
end

end OAI
