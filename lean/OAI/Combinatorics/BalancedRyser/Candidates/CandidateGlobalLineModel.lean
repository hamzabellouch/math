import OAI.Combinatorics.BalancedRyser.Candidates.CandidateGlobalLineTotals
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateLabelBridge
import OAI.Combinatorics.BalancedRyser.Probability.PatternGate

namespace OAI

namespace Balanced.CandidateGlobalLine

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateExposure CandidateIncidence PartialAlignment

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance globalLineModelMeasurableSpace : MeasurableSpace F := ⊤

abbrev lineModel (L : Line F) := allModel (lineHitTest L)

def oldLineTest (L : Line F) (D : Finset (Direction F)) : Test F :=
  fun T _ p => 0 < (exposedTupleIndices T D).card ∧ ∃ i, OnLine (p i) L

theorem allExposed_overlapCount_eq (L : Line F) (D : Finset (Direction F))
    (M : MergedPairs F) :
    (lineModel L).overlapCount ∅ D M = (allModel (oldLineTest L D)).count M := by
  unfold PatternModel.overlapCount PatternModel.count
  apply Finset.sum_congr rfl
  intro a _
  change (if Disjoint (generatorSet a.2.tuple \ ∅) D then 0 else
    (lineModel L).indicator a M) = (allModel (oldLineTest L D)).indicator a M
  simp only [Finset.sdiff_empty]
  by_cases h : Disjoint (generatorSet a.2.tuple) D
  · have hn : ¬ 0 < (exposedTupleIndices a.2.tuple D).card := by
      intro hp
      exact ((not_disjoint_generatorSet_iff a.2.tuple D).mpr hp) h
    simp [h, PatternModel.indicator, allModel, CandidateIncidence.event,
      oldLineTest, hn]
  · have hp := (not_disjoint_generatorSet_iff a.2.tuple D).mp h
    simp [h, PatternModel.indicator, allModel, CandidateIncidence.event,
      oldLineTest, lineHitTest, hp]

theorem lineModel_fixed_count_le (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ)
    (hD : D.card ≤ m) (ha : L ∉ constituentLines a) :
    (lineModel L).fixedExpectation D a (lineModel L).count ≤
      (163840 * (m+1)^4 : ℝ) * Fintype.card F := by
  rw [allModel_fixed_count]
  exact sum_targets_lineSuccess_le L D a m hD ha

theorem lineModel_fixed_allExposed (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (lineModel L).fixedExpectation D a ((lineModel L).overlapCount ∅ D) =
      ∑ g : Direction F,
      ∑ T ∈ (eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card),
        conditionalProbability D a (lineSuccessEvent T g L) := by
  have heq : (lineModel L).overlapCount ∅ D = (allModel (oldLineTest L D)).count :=
    funext (allExposed_overlapCount_eq L D)
  rw [heq]
  change (allModel (oldLineTest L D)).fixedExpectation D a
    (allModel (oldLineTest L D)).count = _
  rw [allModel_fixed_count]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  by_cases h : 0 < (exposedTupleIndices T D).card
  · simp only [oldLineTest, h, true_and, ite_eq_left, lineSuccessEvent]
  · simp [oldLineTest, h, conditionalProbability]

theorem lineModel_fixed_allExposed_le (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ)
    (hD : D.card ≤ m) (ha : L ∉ constituentLines a) :
    (lineModel L).fixedExpectation D a ((lineModel L).overlapCount ∅ D) ≤
      (163840 * (m+1)^4 : ℝ) := by
  rw [lineModel_fixed_allExposed]
  exact sum_targets_overlapping_lineSuccess_le L D a m hD ha

theorem lineModel_fixed_overlap_le (L : Line F)
    (K₀ K : Finset (Direction F)) (a : MergedPairs F) (m : ℕ)
    (hD : (K₀ ∪ K).card ≤ m) (ha : L ∉ constituentLines a) :
    (lineModel L).fixedExpectation (K₀ ∪ K) a ((lineModel L).overlapCount K₀ K) ≤
      (163840 * (m+1)^4 : ℝ) := by
  apply le_trans _ (lineModel_fixed_allExposed_le L (K₀ ∪ K) a m hD ha)
  apply integral_mono
    ((lineModel L).integrable_fixed_overlapCount (K₀ ∪ K) a K₀ K)
    ((lineModel L).integrable_fixed_overlapCount (K₀ ∪ K) a ∅ (K₀ ∪ K))
  intro M
  exact (lineModel L).overlapCount_le_allExposed K₀ K _

omit [Field F] in
theorem lineGate_depends (L : Line F) (M N : MergedPairs F)
    (h : ∀ d ∈ ({L.1} : Finset (Direction F)), M d = N d) :
    L ∉ constituentLines M ↔ L ∉ constituentLines N :=
  CandidateLineGate.not_mem_iff_of_direction_agreement L M N (h L.1 (by simp))

abbrev gatedLineModel (L : Line F) : PatternModel.{u} :=
  (lineModel L).gated {L.1} {M | L ∉ constituentLines M}
    (Set.toFinite _).measurableSet (lineGate_depends L)

theorem gatedLineModel_count (L : Line F) (M : MergedPairs F) :
    (gatedLineModel L).count M =
      if L ∉ constituentLines M then ∑ g : Direction F,
        (tupleCount (lineHitTest L) g M : ℝ) else 0 := by
  rw [PatternModel.gated_count, allModel_count]
  by_cases h : L ∉ constituentLines M
  · simp only [Set.mem_ofPred_eq, ite_eq_left h]
  · simp only [Set.mem_ofPred_eq, ite_eq_right h]

theorem gatedLineModel_measure (L : Line F) :
    (gatedLineModel L).measure = (offsetLaw F).toMeasure := allModel_measure (lineHitTest L)

theorem gatedLineModel_fixedExpectation (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (f : MergedPairs F → ℝ) :
    (gatedLineModel L).fixedExpectation D a f =
      ∫ M, f M ∂(exposedLaw D a).toMeasure := allModel_fixedExpectation (lineHitTest L) D a f

theorem gatedLineModel_initial_mean_le (L : Line F) (a : MergedPairs F) :
    (gatedLineModel L).fixedExpectation {L.1} a (gatedLineModel L).count ≤
      2621440 * (Fintype.card F : ℝ) := by
  rw [PatternModel.gated_fixed_count (lineModel L) {L.1}
    {M | L ∉ constituentLines M} (Set.toFinite _).measurableSet
    (lineGate_depends L) {L.1} (Finset.Subset.refl _) a]
  split_ifs with ha
  · simpa only [Nat.cast_one, show (163840 * (1+1)^4 : ℝ) = 2621440 by norm_num] using
      lineModel_fixed_count_le L {L.1} a 1 (by simp) ha
  · positivity

theorem gatedLineModel_centered_moment_le (L : Line F) (a : MergedPairs F) (s : ℕ) :
    (gatedLineModel L).fixedExpectation {L.1} a
      (fun M => |(gatedLineModel L).count M -
        (gatedLineModel L).fixedExpectation {L.1} a (gatedLineModel L).count| ^ (2*s)) ≤
      ((2*s).factorial : ℝ) * 2^(2*s) *
        (2 * (163840 * ((1 + 10*s : ℕ) + 1)^4 : ℝ))^(2*s) *
          (Fintype.card F : ℝ)^s := by
  apply PatternModel.gated_centered_moment_le (lineModel L) {L.1}
    {M | L ∉ constituentLines M} (Set.toFinite _).measurableSet
    (lineGate_depends L) {L.1} (by rfl) a s 4 (Fintype.card F)
    (163840 * ((1 + 10*s : ℕ) + 1)^4 : ℝ)
    (by exact_mod_cast Fintype.card_pos (α := F)) (by positivity)
    (fun b => (allModel_support_card _ b).le)
  · intro K hK y hy
    apply lineModel_fixed_count_le L ({L.1} ∪ K) y (1 + 10*s) _ hy
    have hc := Finset.card_union_le ({L.1} : Finset (Direction F)) K
    simp only [Finset.card_singleton] at hc hK
    omega
  · intro K hK y hy
    apply lineModel_fixed_overlap_le L {L.1} K y (1 + 10*s) _ hy
    have hc := Finset.card_union_le ({L.1} : Finset (Direction F)) K
    simp only [Finset.card_singleton] at hc hK
    omega

def globalLineMomentConstant (s : ℕ) : ℝ :=
  ((2*s).factorial : ℝ) * 2^(2*s) *
    (2 * (163840 * ((1 + 10*s : ℕ) + 1)^4 : ℝ))^(2*s)

theorem globalLineMomentConstant_nonneg (s : ℕ) : 0 ≤ globalLineMomentConstant s := by
  unfold globalLineMomentConstant
  positivity

theorem gatedLineModel_centered_moment_bound (L : Line F) (a : MergedPairs F) (s : ℕ) :
    (gatedLineModel L).fixedExpectation {L.1} a
      (fun M => |(gatedLineModel L).count M -
        (gatedLineModel L).fixedExpectation {L.1} a (gatedLineModel L).count| ^ (2*s)) ≤
      globalLineMomentConstant s * (Fintype.card F : ℝ)^s :=
  gatedLineModel_centered_moment_le L a s

end
end Balanced.CandidateGlobalLine

end OAI
