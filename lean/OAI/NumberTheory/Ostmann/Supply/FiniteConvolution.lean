import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] [Fintype G]
local notation "H" => EuclideanSpace ℂ G

def translation (z : G) : H ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.addRight z)

@[simp] theorem translation_apply (z : G) (f : H) (x : G) :
    translation z f x = f (x-z) := by
  simp [translation, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', sub_eq_add_neg]

def convolutionOperator (b : G → ℂ) : H →L[ℂ] H :=
  ∑ z, b z • (translation z).toContinuousLinearEquiv.toContinuousLinearMap

theorem convolutionOperator_apply (b : G → ℂ) (f : H) (x : G) :
    convolutionOperator b f x = ∑ z, b z * f (x-z) := by
  simp only [convolutionOperator, sum_apply,
    smul_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    translation_apply, smul_eq_mul]

theorem convolutionOperator_matrix (b : G → ℂ) (f : H) (x : G) :
    convolutionOperator b f x = ∑ y, b (x-y) * f y := by
  rw [convolutionOperator_apply]
  apply Fintype.sum_equiv (Equiv.subLeft x)
  intro z
  simp

theorem convolutionOperator_norm_le (b : G → ℂ) :
    ‖convolutionOperator b‖ ≤ ∑ z, ‖b z‖ := by
  refine (convolutionOperator b).opNorm_le_bound
    (Finset.sum_nonneg fun _ _ => norm_nonneg _) (fun f => ?_)
  simp only [convolutionOperator, sum_apply, smul_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe]
  calc
    _ ≤ ∑ z, ‖b z • translation z f‖ := norm_sum_le _ _
    _ = (∑ z, ‖b z‖)*‖f‖ := by simp [norm_smul, ← Finset.sum_mul]

end Ostmann.Supply

end

end OAI
