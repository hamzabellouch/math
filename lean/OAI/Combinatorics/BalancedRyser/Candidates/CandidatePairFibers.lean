import OAI.Combinatorics.BalancedRyser.Candidates.CandidateLabelBridge
import OAI.Combinatorics.BalancedRyser.Candidates.CandidatePairCounts
import OAI.Combinatorics.BalancedRyser.Candidates.CandidatePairPatternModel
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateRootFibers

namespace OAI

namespace Balanced.CandidatePairs
noncomputable section
open scoped Classical BigOperators
open CandidateExposure TupleAlignment
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def successfulPairs (g : Direction F) (M : MergedPairs F) : Finset (EligiblePair g) :=
  Finset.univ.filter (fun a => M ∈ pairSuccessEvent g a)

theorem sum_partner_eq_pair_card (g : Direction F) (M : MergedPairs F)
    (R : FourTuple F → Prop) :
    (∑ T ∈ (eligibleTuples g).filter R,
      if M ∈ successfulInDirection T g then lineCount M (targetLine g T M) else 0) =
      ((successfulPairs g M).filter (fun a => R a.1.val)).card := by
  have hline (T : FourTuple F) :
      lineCount M (targetLine g T M) =
        ∑ U : ↥(eligibleTuples g),
          if (∀ i, OnLine (tuplePoint M U.val i) (targetLine g T M)) ∧
            Function.Injective (tuplePoint M U.val) then 1 else 0 := by
    unfold lineCount lineTuples
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_subtype (eligibleTuples g)
      (p := fun U => U ∈ eligibleTuples g) (F := inferInstance) (fun _ => Iff.rfl)
      (fun tuple => if (∀ index, OnLine (tuplePoint M tuple index) (targetLine g T M)) ∧
        Function.Injective (tuplePoint M tuple) then (1 : ℕ) else 0)
  have hs := Finset.sum_subtype (eligibleTuples g)
    (p := fun T => T ∈ eligibleTuples g) (F := inferInstance) (fun _ => Iff.rfl)
    (fun T => if R T then
      (if M ∈ successfulInDirection T g then lineCount M (targetLine g T M) else 0) else 0)
  rw [Finset.sum_filter, hs]
  simp_rw [hline]
  simp only [successfulPairs, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hR : R T.val <;> by_cases hT : M ∈ successfulInDirection T.val g
  all_goals simp only [hR, hT, ite_true, ite_false]
  · apply Finset.sum_congr rfl
    intro U _
    simp only [mem_pairSuccessEvent_iff, hT, true_and, targetLine]
    split_ifs with hsuccess <;> simp [hsuccess]
  · symm
    apply Finset.sum_eq_zero
    intro U _
    simp only [mem_pairSuccessEvent_iff, hT, false_and, ite_false]
  · symm
    apply Finset.sum_eq_zero
    intro U _
    simp
  · symm
    apply Finset.sum_eq_zero
    intro U _
    simp

theorem pairCount_eq_successfulPairs_card (g : Direction F) (M : MergedPairs F) :
    pairCount g M = (successfulPairs g M).card := by
  simpa only [pairCount, Finset.filter_true] using
    sum_partner_eq_pair_card g M (fun _ => True)

theorem successfulPairs_card_eq_rootFiberSquareCount (g : Direction F) (M : MergedPairs F) :
    (successfulPairs g M).card = rootFiberSquareCount M g := by
  let e : EligiblePair g ≃ RootPrescription g × RootPrescription g :=
    Equiv.prodCongr (eligibleTupleEquivRootPrescription g)
      (eligibleTupleEquivRootPrescription g)
  have hevent (a : EligiblePair g) :
      M ∈ pairSuccessEvent g a ↔ e a ∈ commonLineSuccessPairs M g := by
    rw [mem_commonLineSuccessPairs_iff]
    simp only [e, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, equivRootPrescription_tuple,
      pairSuccessEvent, Set.mem_ofPred_eq]
  rw [rootFiberSquareCount_eq_pair_card]
  have h := Equiv.sum_comp e
    (fun ab => if ab ∈ commonLineSuccessPairs M g then (1 : ℕ) else 0)
  have hc : (Finset.univ.filter (fun ab : RootPrescription g × RootPrescription g =>
      ab ∈ commonLineSuccessPairs M g)) = commonLineSuccessPairs M g := by
    ext ab
    simp
  rw [← hc]
  simpa only [successfulPairs, Finset.card_eq_sum_ones, Finset.sum_filter, ← hevent] using h

theorem pairCount_eq_rootFiberSquareCount (g : Direction F) (M : MergedPairs F) :
    pairCount g M = rootFiberSquareCount M g :=
  (pairCount_eq_successfulPairs_card g M).trans
    (successfulPairs_card_eq_rootFiberSquareCount g M)

theorem pairPatternModel_count_eq_pairCount (g : Direction F) (M : MergedPairs F) :
    (pairPatternModel g).count M = (pairCount g M : ℝ) := by
  rw [pairPatternModel_count, pairCount_eq_successfulPairs_card]
  rfl

theorem firstOverlapPairCount_eq_card (D : Finset (Direction F))
    (g : Direction F) (M : MergedPairs F) :
    firstOverlapPairCount D g M =
      ((successfulPairs g M).filter
        (fun a => ¬ Disjoint (generatorSet a.1.val) D)).card := by
  have h := sum_partner_eq_pair_card g M
    (fun T => 0 < (PartialAlignment.exposedTupleIndices T D).card)
  convert h using 1
  · unfold firstOverlapPairCount
    apply Finset.sum_congr
    · ext T
      simp
    · intro T hT
      split_ifs <;> rfl
  · congr 1
    ext a
    simp only [Finset.mem_filter, not_disjoint_generatorSet_iff]

theorem swap_mem_successfulPairs (g : Direction F) (M : MergedPairs F)
    (a : EligiblePair g) : a.swap ∈ successfulPairs g M ↔ a ∈ successfulPairs g M := by
  simp only [successfulPairs, Finset.mem_filter, Finset.mem_univ, true_and,
    pairSuccessEvent_swap]

theorem second_overlap_card_eq_first (D : Finset (Direction F))
    (g : Direction F) (M : MergedPairs F) :
    ((successfulPairs g M).filter
      (fun a => ¬ Disjoint (generatorSet a.2.val) D)).card =
    ((successfulPairs g M).filter
      (fun a => ¬ Disjoint (generatorSet a.1.val) D)).card := by
  apply Finset.card_bij (fun a _ => a.swap)
  · intro a ha
    obtain ⟨hs, ho⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨(swap_mem_successfulPairs g M a).mpr hs, ho⟩
  · intro a ha b hb hab
    exact Prod.swap_injective hab
  · intro a ha
    obtain ⟨hs, ho⟩ := Finset.mem_filter.mp ha
    exact ⟨a.swap, Finset.mem_filter.mpr
      ⟨(swap_mem_successfulPairs g M a).mpr hs, ho⟩, Prod.swap_swap a⟩

theorem pairPatternModel_allExposed_overlap_le (D : Finset (Direction F))
    (g : Direction F) (M : MergedPairs F) :
    (pairPatternModel g).overlapCount ∅ D M ≤
      2 * (firstOverlapPairCount D g M : ℝ) := by
  let A := (successfulPairs g M).filter
    (fun a => ¬ Disjoint (generatorSet a.1.val) D)
  let B := (successfulPairs g M).filter
    (fun a => ¬ Disjoint (generatorSet a.2.val) D)
  let U := Finset.univ.filter (fun a : EligiblePair g =>
    ¬ Disjoint (generatorSet a.1.val ∪ generatorSet a.2.val) D ∧
      M ∈ pairSuccessEvent g a)
  have hsub : U ⊆ A ∪ B := by
    intro a ha
    obtain ⟨_, ho, hs⟩ := Finset.mem_filter.mp ha
    have hsuccess : a ∈ successfulPairs g M := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hs⟩
    by_cases hfirst : Disjoint (generatorSet a.1.val) D
    · apply Finset.mem_union_right
      refine Finset.mem_filter.mpr ⟨hsuccess, ?_⟩
      intro hsecond
      exact ho (Finset.disjoint_union_left.mpr ⟨hfirst, hsecond⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hsuccess, hfirst⟩)
  have hcard : U.card ≤ 2 * firstOverlapPairCount D g M := by
    calc
      U.card ≤ (A ∪ B).card := Finset.card_le_card hsub
      _ ≤ A.card + B.card := Finset.card_union_le _ _
      _ = 2 * firstOverlapPairCount D g M := by
        dsimp [A, B]
        rw [second_overlap_card_eq_first, ← firstOverlapPairCount_eq_card]
        omega
  rw [pairPatternModel_overlapCount]
  simp only [Finset.sdiff_empty]
  exact_mod_cast hcard

end
end Balanced.CandidatePairs

end OAI
