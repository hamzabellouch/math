import OAI.Probability.SATComputability.SupercriticalProbability
import OAI.Probability.SATComputability.MaskDeletionTimes

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Classical NNReal

theorem candidate_budget_survival {n m r : ℕ} (cs : Fin m → Fin 3 → SignedLiteral n) :
    (candidateResidual (deletionBudgetMask n r) cs).Nonempty ↔
      deletionSatisfiable r (fun j l => (cs j l).1) (fun j l => (cs j l).2) := by
  rw [deletionSatisfiable_iff_candidate]
  simp only [candidateResidual, deletionBudgetMask, Finset.filter_nonempty_iff,
    Finset.mem_filter, Finset.mem_univ, true_and, not_forall, Prod.eta]

theorem candidate_zero_survival {n m : ℕ} (cs : Fin m → Fin 3 → SignedLiteral n) :
    (candidateResidual (deletionBudgetMask n 0) cs).Nonempty ↔
      (Finset.univ.filter (fun s : Assignment n => ∀ j, auxiliarySatisfies s (cs j))).Nonempty := by
  rw [candidate_budget_survival]
  simp only [Finset.filter_nonempty_iff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨D,hD,s,hs⟩
    have hD0 : D = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hD)
    subst D
    exact ⟨s,fun j => by simpa [auxiliarySatisfies, relaxedClauseSatisfied] using hs j⟩
  · rintro ⟨s,hs⟩
    exact ⟨∅,by simp,s,fun j => Or.inr (hs j)⟩

theorem finite_uniform_expect_eq_mean {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    (FiniteLaw.uniform : FiniteLaw A).expect f = uniformMean f := by
  simp only [FiniteLaw.expect, FiniteLaw.uniform, uniformMean,
    div_eq_mul_inv, Finset.sum_mul, mul_comm]

theorem candidateStep_zero_survival {n : ℕ} [NeZero n] (m : ℕ) :
    (candidateStep (n := n) 3)^[m] candidateAlive (deletionBudgetMask n 0) =
      auxiliaryProbability n 3 m := by
  rw [candidateStep_iterate, finite_uniform_expect_eq_mean]
  unfold auxiliaryProbability auxiliarySurvival auxiliaryAverage embeddedAverage
  rw [finiteClauseAverage_iterate]
  apply uniformMean_congr
  intro cs
  unfold candidateAlive alive
  congr 1
  exact propext (candidate_zero_survival cs)

theorem candidateBlock_zero_survival {n : ℕ} [NeZero n] (r : ℝ≥0) :
    (candidateBlock r 3 (deletionBudgetMask n 0)).expect candidateAlive =
      ∫ m : ℕ, auxiliaryProbability n 3 m ∂poissonMeasure r := by
  rw [candidateBlock_expect]
  simp only [candidateStep_zero_survival]

theorem candidate_full_nonempty {n m : ℕ} (cs : Fin m → Fin 3 → SignedLiteral n) :
    (candidateResidual Finset.univ cs).Nonempty := by
  refine ⟨fun _ => none, ?_⟩
  simp only [candidateResidual, Finset.mem_filter, Finset.mem_univ, true_and]
  intro j hj
  have h := hj 0
  simp [literalFalse] at h

theorem candidate_minimumDeletions_le {n m : ℕ} (cs : Fin m → RelaxedClause n) :
    minimumDeletions (candidateResidual Finset.univ (fun j l => ((cs j).1 l, (cs j).2 l))) ≤
      clauseMinimum cs := by
  obtain ⟨s,hs⟩ := relaxedMinimum_attained (fun j => (cs j).1) (fun j => (cs j).2)
  have hd := delete_one_per_violation s (fun j => (cs j).1) (fun j => (cs j).2)
  change relaxedViolations s (fun j => (cs j).1) (fun j => (cs j).2) = clauseMinimum cs at hs
  rw [hs] at hd
  rw [deletionSatisfiable_iff_candidate] at hd
  obtain ⟨x,hx,hxs⟩ := hd
  apply (minimumDeletions_le_iff (candidate_full_nonempty _)).mpr
  refine ⟨x, ?_, hx⟩
  simp only [candidateResidual, Finset.mem_filter, Finset.mem_univ, true_and]
  intro j hj
  obtain ⟨l,hl⟩ := hxs j
  exact hl (hj l)

end FixedClauseThreshold.Computability

end OAI
