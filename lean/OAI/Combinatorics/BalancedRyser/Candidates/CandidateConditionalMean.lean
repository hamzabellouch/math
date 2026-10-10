import OAI.Combinatorics.BalancedRyser.Candidates.CandidateFirstMoment

namespace OAI

namespace Balanced.CandidateExposure

noncomputable section
open scoped Classical BigOperators
open MeasureTheory PartialAlignment

section FiniteMean
variable {Ω A : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

theorem integral_eventCount_eq_sum (p : PMF Ω) (s : Finset A) (E : A → Set Ω) :
    (∫ ω, ((s.filter (fun a => ω ∈ E a)).card : ℝ) ∂p.toMeasure) =
      ∑ a ∈ s, (p.toOuterMeasure (E a)).toReal := by
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [PMF.toOuterMeasure_apply_fintype,
    ENNReal.toReal_sum (fun ω _ => by
      by_cases h : ω ∈ E a
      · simpa only [Set.indicator_of_mem h] using p.apply_ne_top ω
      · simp [Set.indicator_of_notMem h])]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : ω ∈ E a <;> simp [h]
end FiniteMean

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def successfulTupleCount (g : Direction F) (M : MergedPairs F) : ℕ :=
  ((eligibleTuples g).filter (fun T => M ∈ successfulInDirection T g)).card

def overlappingTupleCount (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) : ℕ :=
  (((eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card)).filter
    (fun T => M ∈ successfulInDirection T g)).card

section Measurable
variable [MeasurableSpace F] [MeasurableSingletonClass F]

theorem integral_successfulTupleCount (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (∫ M, (successfulTupleCount g M : ℝ) ∂(exposedLaw D a).toMeasure) =
      successProbabilitySum g D a := by
  exact integral_eventCount_eq_sum (exposedLaw D a) (eligibleTuples g)
    (fun T => successfulInDirection T g)

theorem integral_overlappingTupleCount (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (∫ M, (overlappingTupleCount g D M : ℝ) ∂(exposedLaw D a).toMeasure) =
      overlapProbabilitySum g D a := by
  exact integral_eventCount_eq_sum (exposedLaw D a)
    ((eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card))
    (fun T => successfulInDirection T g)

theorem conditional_successfulTupleCount_le (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∫ M, (successfulTupleCount g M : ℝ) ∂(exposedLaw D a).toMeasure) ≤
      (20480 * (m + 1) ^ 4 : ℝ) * Fintype.card F := by
  rw [integral_successfulTupleCount]
  exact successProbabilitySum_le g D a m hD

theorem conditional_overlappingTupleCount_le (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∫ M, (overlappingTupleCount g D M : ℝ) ∂(exposedLaw D a).toMeasure) ≤
      (16384 * (m + 1) ^ 4 : ℝ) := by
  rw [integral_overlappingTupleCount]
  exact overlapProbabilitySum_le g D a m hD
end Measurable

end
end Balanced.CandidateExposure

end OAI
