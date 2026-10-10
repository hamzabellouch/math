import OAI.Combinatorics.BalancedRyser.Candidates.CandidateRootCount
import OAI.Combinatorics.BalancedRyser.Probability.RootPatternModel

namespace OAI

namespace Balanced.CandidateExposure

noncomputable section
open scoped Classical BigOperators
open TupleAlignment PartialAlignment MeasureTheory

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [Fintype F] in

theorem not_disjoint_generatorSet_iff (T : FourTuple F) (D : Finset (Direction F)) :
    ¬ Disjoint (generatorSet T) D ↔ 0 < (exposedTupleIndices T D).card := by
  rw [Finset.not_disjoint_iff, Finset.card_pos]
  constructor
  · rintro ⟨d, hd, hD⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hD⟩⟩
  · rintro ⟨i, hi⟩
    exact ⟨T.generator i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
      (Finset.mem_filter.mp hi).2⟩

theorem rootOverlapCount_empty_eq_overlappingTupleCount (g : Direction F)
    (D : Finset (Direction F)) (M : MergedPairs F) :
    TupleAlignment.rootOverlapCount g ∅ D M = overlappingTupleCount g D M := by
  unfold TupleAlignment.rootOverlapCount overlappingTupleCount
  simp only [Finset.sdiff_empty]
  apply Finset.card_bij (fun a _ => a.tuple)
  · intro a ha
    obtain ⟨_, hover, hs⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨
      ((eligibleTupleEquivRootPrescription g).symm a).2, ?_⟩, hs⟩
    exact (not_disjoint_generatorSet_iff a.tuple D).mp hover
  · intro a ha b hb hab
    apply (eligibleTupleEquivRootPrescription g).symm.injective
    exact Subtype.ext hab
  · intro T hT
    obtain ⟨hT, hs⟩ := Finset.mem_filter.mp hT
    obtain ⟨hg, hover⟩ := Finset.mem_filter.mp hT
    let a := eligibleTupleEquivRootPrescription g ⟨T, hg⟩
    have ha : a.tuple = T := equivRootPrescription_tuple g ⟨T, hg⟩
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ha⟩
    · rw [ha]
      exact (not_disjoint_generatorSet_iff T D).mpr hover
    · change M ∈ successfulInDirection a.tuple g
      simpa only [ha] using hs

theorem rootPatternModel_allExposed_overlapCount (g : Direction F)
    (D : Finset (Direction F)) (M : MergedPairs F) :
    (rootPatternModel g).overlapCount ∅ D M =
      (overlappingTupleCount g D M : ℝ) := by
  rw [rootPatternModel_overlapCount, rootOverlapCount_empty_eq_overlappingTupleCount]

local instance candidateLabelMeasurableSpace : MeasurableSpace F := ⊤

theorem rootPatternModel_fixed_count_le (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (rootPatternModel g).fixedExpectation D a (rootPatternModel g).count ≤
      (20480 * (m + 1) ^ 4 : ℝ) * Fintype.card F := by
  rw [rootPatternModel_fixed_count_exposed]
  simp_rw [← successfulTupleCount_eq_rootSuccessCount]
  exact conditional_successfulTupleCount_le g D a m hD

theorem rootPatternModel_fixed_allExposed_overlapCount_le (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (rootPatternModel g).fixedExpectation D a
      ((rootPatternModel g).overlapCount ∅ D) ≤ (16384 * (m + 1) ^ 4 : ℝ) := by
  rw [rootPatternModel_fixed_overlapCount]
  simp_rw [rootOverlapCount_empty_eq_overlappingTupleCount]
  exact conditional_overlappingTupleCount_le g D a m hD

end
end Balanced.CandidateExposure

end OAI
