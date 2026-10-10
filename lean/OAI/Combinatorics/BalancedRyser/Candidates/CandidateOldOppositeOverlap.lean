import OAI.Combinatorics.BalancedRyser.Candidates.CandidateConditionalMean
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateValidityWitness

namespace OAI

namespace Balanced.CandidateOldOpposite

noncomputable section
open scoped Classical BigOperators
open CandidateExposure CandidateValidityWitness PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def overlappingWitnesses (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) : Finset ((FourTuple F × Fin 4) × Direction F) :=
  (((((eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card)).filter
    (fun T => M ∈ successfulInDirection T g)).product Finset.univ).product D).filter
    (fun w => w.2 ≠ g ∧ w.2 ∉ generatorSet w.1.1 ∧
      PairWitness M w.2 (tuplePoint M w.1.1 w.1.2)
        (tuplePoint M w.1.1 (w.1.2 + 2)))

theorem mem_overlappingWitnesses_iff (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) (T : FourTuple F) (i : Fin 4) (d : Direction F) :
    ((T, i), d) ∈ overlappingWitnesses g D M ↔
      T ∈ eligibleTuples g ∧ 0 < (exposedTupleIndices T D).card ∧
      M ∈ successfulInDirection T g ∧ d ∈ D ∧ d ≠ g ∧
      d ∉ generatorSet T ∧ PairWitness M d (tuplePoint M T i)
        (tuplePoint M T (i + 2)) := by
  simp only [overlappingWitnesses, Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
    Finset.mem_univ, and_true]
  tauto

theorem card_overlappingWitnesses_le (g : Direction F)
    (D : Finset (Direction F)) (M : MergedPairs F) :
    (overlappingWitnesses g D M).card ≤ 4 * D.card * overlappingTupleCount g D M := by
  unfold overlappingWitnesses
  calc
    _ ≤ (((((eligibleTuples g).filter (fun T =>
        0 < (exposedTupleIndices T D).card)).filter
        (fun T => M ∈ successfulInDirection T g)).product
        (Finset.univ : Finset (Fin 4))).product D).card := Finset.card_filter_le _ _
    _ = _ := by
      simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ, Fintype.card_fin,
        overlappingTupleCount]
      ring

theorem expected_overlappingWitnesses_le (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∑ M : MergedPairs F, (exposedLaw D a M).toReal *
      ((overlappingWitnesses g D M).card : ℝ)) ≤
      65536 * (m : ℝ) * ((m : ℝ) + 1)^4 := by
  let : MeasurableSpace F := ⊤
  have hmean := conditional_overlappingTupleCount_le g D a m hD
  rw [PMF.integral_eq_sum] at hmean
  simp only [smul_eq_mul] at hmean
  have hcard (M : MergedPairs F) : ((overlappingWitnesses g D M).card : ℝ) ≤
      (4 * (m : ℝ)) * (overlappingTupleCount g D M : ℝ) := by
    exact_mod_cast (card_overlappingWitnesses_le g D M).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hD))
  calc
    _ ≤ ∑ M : MergedPairs F, (exposedLaw D a M).toReal *
        ((4 * (m : ℝ)) * (overlappingTupleCount g D M : ℝ)) := by
      apply Finset.sum_le_sum
      intro M _
      exact mul_le_mul_of_nonneg_left (hcard M) ENNReal.toReal_nonneg
    _ = (4 * (m : ℝ)) * ∑ M : MergedPairs F, (exposedLaw D a M).toReal *
        (overlappingTupleCount g D M : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M _
      ring
    _ ≤ (4 * (m : ℝ)) * (16384 * ((m : ℝ) + 1)^4) :=
      mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = _ := by ring

end
end Balanced.CandidateOldOpposite

end OAI
