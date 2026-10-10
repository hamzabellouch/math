import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

namespace OAI

namespace Balanced
open scoped _root_.Balanced

theorem uniform_filter_eq_subtype_map {α : Type*} [Fintype α] [Nonempty α]
    (s : Set α) [Fintype s] [Nonempty s]
    (h : ∃ a ∈ s, a ∈ (PMF.uniformOfFintype α).support) :
    (PMF.uniformOfFintype α).filter s h =
      (PMF.uniformOfFintype s).map Subtype.val := by
  classical
  ext a
  by_cases ha : a ∈ s
  · have hmap : ((PMF.uniformOfFintype s).map Subtype.val) a =
        (Fintype.card s : ENNReal)⁻¹ := by
      rw [PMF.map_apply]
      rw [tsum_eq_single (⟨a, ha⟩ : s)]
      · simp
      · intro b hb
        rw [ite_eq_right]
        intro hab
        exact hb (Subtype.ext hab.symm)
    rw [hmap, PMF.filter_apply, ← PMF.toOuterMeasure_apply,
      PMF.toOuterMeasure_uniformOfFintype_apply, Set.indicator_of_mem ha,
      PMF.uniformOfFintype_apply]
    have hq0 : (Fintype.card α : ENNReal) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hqtop : (Fintype.card α : ENNReal) ≠ ⊤ := by simp
    have hs0 : (Fintype.card s : ENNReal) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hstop : (Fintype.card s : ENNReal) ≠ ⊤ := by simp
    rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hs0) (Or.inl hstop), inv_inv]
    calc
      (Fintype.card α : ENNReal)⁻¹ *
          ((Fintype.card s : ENNReal)⁻¹ * Fintype.card α) =
        (Fintype.card s : ENNReal)⁻¹ *
          ((Fintype.card α : ENNReal)⁻¹ * Fintype.card α) := by ac_rfl
      _ = _ := by rw [ENNReal.inv_mul_cancel hq0 hqtop, mul_one]
  · rw [PMF.filter_apply_eq_zero_of_notMem h ha, PMF.map_apply]
    symm
    apply ENNReal.tsum_eq_zero.mpr
    intro b
    rw [ite_eq_right]
    intro hab
    exact ha (hab ▸ b.2)

end Balanced

end OAI
