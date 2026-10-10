import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace OAI

open scoped ENNReal
namespace Balanced
open scoped _root_.Balanced

theorem map_filter_preimage {α β : Type*} (p : PMF α) (f : α → β)
    (s : Set β)
    (ha : ∃ a ∈ f ⁻¹' s, a ∈ p.support)
    (hb : ∃ b ∈ s, b ∈ (p.map f).support) :
    (p.filter (f ⁻¹' s) ha).map f = (p.map f).filter s hb := by
  classical
  ext b
  rw [PMF.map_apply, PMF.filter_apply, ← PMF.toOuterMeasure_apply,
    PMF.toOuterMeasure_map_apply]
  simp only [PMF.filter_apply, ← PMF.toOuterMeasure_apply]
  by_cases hbs : b ∈ s
  · rw [Set.indicator_of_mem hbs, PMF.map_apply, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro a
    by_cases hba : b = f a
    · subst b
      simp [hbs]
    · simp [hba]
  · rw [Set.indicator_of_notMem hbs, zero_mul]
    apply ENNReal.tsum_eq_zero.mpr
    intro a
    by_cases hba : b = f a
    · subst b
      simp [hbs]
    · simp [hba]
end Balanced

end OAI
