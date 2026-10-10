import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Deletion.Deletion

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open scoped BigOperators

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F] {k : ℕ}

theorem deletion_sum_real_mass (Q : PMF (DeletionSet F k)) :
    ∑ D, (Q D).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun D _ => Q.apply_ne_top D)]
  have hsum : ∑ D, Q D = 1 := by simpa only [tsum_fintype] using Q.tsum_coe
  rw [hsum]
  simp

theorem deletionEventProbability_eq_outerMeasure (Q : PMF (DeletionSet F k))
    (E : DeletionSet F k → Prop) :
    deletionEventProbability Q E = (Q.toOuterMeasure {D | E D}).toReal := by
  classical
  rw [PMF.toOuterMeasure_apply, tsum_fintype]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro D _
    by_cases h : E D <;> simp [Set.indicator, h]
  · intro D _
    by_cases h : E D <;> simp [Set.indicator, h, Q.apply_ne_top]

 theorem deletionEventProbability_nonneg (Q : PMF (DeletionSet F k))
    (E : DeletionSet F k → Prop) : 0 ≤ deletionEventProbability Q E := by
  classical
  unfold deletionEventProbability
  exact Finset.sum_nonneg fun D _ => by split_ifs <;> positivity

 theorem deletionEventProbability_mono (Q : PMF (DeletionSet F k))
    {E G : DeletionSet F k → Prop} (hEG : ∀ D, E D → G D) :
    deletionEventProbability Q E ≤ deletionEventProbability Q G := by
  classical
  unfold deletionEventProbability
  apply Finset.sum_le_sum
  intro D _
  by_cases he : E D
  · simp [he, hEG D he]
  · simp only [he, ite_false]
    split_ifs <;> positivity

 theorem deletionEventProbability_true (Q : PMF (DeletionSet F k)) :
    deletionEventProbability Q (fun _ => True) = 1 := by
  classical
  simpa [deletionEventProbability] using deletion_sum_real_mass Q

 theorem deletionEventProbability_le_one (Q : PMF (DeletionSet F k))
    (E : DeletionSet F k → Prop) : deletionEventProbability Q E ≤ 1 := by
  rw [← deletionEventProbability_true Q]
  exact deletionEventProbability_mono Q (fun _ _ => True.intro)

theorem deletionEventProbability_le_uniform {K : ℝ} (Q : PMF (DeletionSet F k))
    (hdom : DeletionDominated k K Q) (E : DeletionSet F k → Prop) :
    deletionEventProbability Q E ≤
      Real.exp (K * (Fintype.card F : ℝ)) *
        (deletionEventCard E : ℝ) / (Fintype.card (DeletionSet F k) : ℝ) := by
  classical
  calc
    deletionEventProbability Q E ≤
        ∑ D : DeletionSet F k, if E D then
          Real.exp (K * (Fintype.card F : ℝ)) * uniformDeletionMass (F := F) k
        else 0 := by
      unfold deletionEventProbability
      apply Finset.sum_le_sum
      intro D _
      split_ifs with h
      · exact hdom D
      · rfl
    _ = _ := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, uniformDeletionMass]
      unfold deletionEventCard
      ring

theorem deletionEventProbability_or_le (Q : PMF (DeletionSet F k))
    (E G : DeletionSet F k → Prop) :
    deletionEventProbability Q (fun D => E D ∨ G D) ≤
      deletionEventProbability Q E + deletionEventProbability Q G := by
  classical
  unfold deletionEventProbability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro D _
  by_cases he : E D <;> by_cases hg : G D <;> simp [he, hg]

theorem uniformDeletionMass_eq_pmf [Nonempty (DeletionSet F k)] (D : DeletionSet F k) :
    uniformDeletionMass (F := F) k = (PMF.uniformOfFintype (DeletionSet F k) D).toReal := by
  simp [uniformDeletionMass, PMF.uniformOfFintype_apply]

theorem deletionEventProbability_uniform [Nonempty (DeletionSet F k)]
    (E : DeletionSet F k → Prop) :
    deletionEventProbability (PMF.uniformOfFintype (DeletionSet F k)) E =
      (deletionEventCard E : ℝ) / (Fintype.card (DeletionSet F k) : ℝ) := by
  classical
  unfold deletionEventProbability
  simp_rw [← uniformDeletionMass_eq_pmf]
  rw [← Finset.sum_filter]
  simp [uniformDeletionMass, deletionEventCard, div_eq_mul_inv]

end Balanced

end OAI
