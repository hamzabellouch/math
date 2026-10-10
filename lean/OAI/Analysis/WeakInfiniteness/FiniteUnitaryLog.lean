import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint

namespace WeakPureInfiniteness

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

def finiteContinuousEndAlgEquiv : (H →ₗ[ℂ] H) ≃ₐ[ℂ] (H →L[ℂ] H) :=
  { LinearMap.toContinuousLinearMap with
    map_mul' := fun _ _ => rfl
    commutes' := fun _ => rfl }

lemma finite_spectrum_continuousEnd (T : H →L[ℂ] H) : (spectrum ℂ T).Finite := by
  rw [← finiteContinuousEndAlgEquiv.apply_symm_apply T, AlgEquiv.spectrum_eq]
  exact Module.End.finite_spectrum _

lemma finite_expUnitary_argSelfAdjoint (u : unitary (H →L[ℂ] H)) :
    expUnitary (Unitary.argSelfAdjoint u) = u := by
  let : CompleteSpace H := FiniteDimensional.complete ℂ H
  apply Subtype.ext
  have : ContinuousOn arg (spectrum ℂ (u : H →L[ℂ] H)) :=
    (finite_spectrum_continuousEnd _).continuousOn _
  rw [expUnitary_coe, Unitary.argSelfAdjoint_coe, ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ),
    ← cfc_comp_smul .., ← cfc_comp' ..]
  conv_rhs => rw [← cfc_id' ℂ (u : H →L[ℂ] H)]
  refine cfc_congr fun y hy ↦ ?_
  have hy₁ : ‖y‖ = 1 := spectrum.norm_eq_one_of_unitary u.2 hy
  have hh : I * y.arg = log y :=
    Complex.ext (by simp [log_re, hy₁]) (by simp [log_im])
  simpa [← exp_eq_exp_ℂ, hh] using exp_log (by aesop)

end WeakPureInfiniteness
end

end OAI
