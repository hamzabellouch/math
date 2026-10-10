import OAI.Analysis.Pureness.Operators.PositiveStateExtension
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_positiveState_norming [Nontrivial A] (a : A) (ha : 0 ≤ a) :
    ∃ f : A →ₚ[ℂ] ℂ, f 1 = 1 ∧ f a = (‖a‖ : ℂ) := by
  have han : IsStarNormal a := (IsSelfAdjoint.of_nonneg ha).isStarNormal
  let s : spectrum ℂ a := ⟨(‖a‖ : ℂ), by
    exact spectrum.algebraMap_mem ℂ (CStarAlgebra.norm_mem_spectrum_of_nonneg a ha)⟩
  let ev : C(spectrum ℂ a, ℂ) →ₚ[ℂ] ℂ :=
    PositiveLinearMap.mk₀ (ContinuousMap.evalAlgHom ℂ ℂ s).toLinearMap (fun b hb => hb s)
  have hev : ev 1 = 1 := rfl
  obtain ⟨f, hf1, hf⟩ := exists_positiveState_extension (cfcHom han)
    (cfcHom_injective han) ev hev
  refine ⟨f, hf1, ?_⟩
  calc
    f a = ev ((ContinuousMap.id ℂ).restrict (spectrum ℂ a)) := by
      simpa only [cfcHom_id] using hf ((ContinuousMap.id ℂ).restrict (spectrum ℂ a))
    _ = (‖a‖ : ℂ) := rfl

theorem positive_eq_zero_of_states [Nontrivial A] (a : A) (ha : 0 ≤ a)
    (h : ∀ f : A →ₚ[ℂ] ℂ, f 1 = 1 → f a = 0) : a = 0 := by
  obtain ⟨f, hf1, hfa⟩ := exists_positiveState_norming a ha
  have hn : (‖a‖ : ℂ) = 0 := hfa.symm.trans (h f hf1)
  exact norm_eq_zero.mp (Complex.ofReal_eq_zero.mp hn)

theorem stateGNS_separates [Nontrivial A] (a : A)
    (h : ∀ f : A →ₚ[ℂ] ℂ, f 1 = 1 → f.gnsStarAlgHom a = 0) : a = 0 := by
  apply (CStarRing.star_mul_self_eq_zero_iff a).mp
  apply positive_eq_zero_of_states (star a * a) (star_mul_self_nonneg a)
  intro f hf1
  rw [← stateGNS_vector_value f, map_mul, map_star, h f hf1, star_zero, mul_zero]
  simp
end CuntzPureness

end

end OAI
