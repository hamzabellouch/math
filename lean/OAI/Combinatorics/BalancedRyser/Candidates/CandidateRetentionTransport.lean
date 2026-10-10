import OAI.Combinatorics.BalancedRyser.Candidates.CandidateSecondary
import OAI.Combinatorics.BalancedRyser.Probability.RootSuccess

namespace OAI

namespace Balanced.CandidateRetentionTransport

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def successfulChoices (M : MergedPairs F) : Finset (SplitChoice F) :=
  Finset.univ.filter fun C =>
    Function.Injective C.tuple.generator ∧
    (∀ i, C.tuple.generator i ≠ C.line.1) ∧
    Function.Injective (tuplePoint M C.tuple) ∧
    ∀ i, OnLine (tuplePoint M C.tuple i) C.line

def successfulTest (M : MergedPairs F) (P : SplitChoice F → Prop) :
    Finset (SplitChoice F) := (successfulChoices M).filter P

@[simp] theorem mem_successfulTest (M : MergedPairs F) (P : SplitChoice F → Prop)
    (C : SplitChoice F) :
    C ∈ successfulTest M P ↔ C ∈ successfulChoices M ∧ P C := by
  simp only [successfulTest, Finset.mem_filter]

theorem valid_mem_successfulChoices {M : MergedPairs F} {g : Direction F}
    {C : SplitChoice F} (h : ValidChoice M g C) : C ∈ successfulChoices M := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, h.2.2.1, ?_, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  simpa only [h.1] using h.2.2.2.1

theorem retained_filter_card_le_two (M : MergedPairs F) (P : SplitChoice F → Prop)
    (all : Finset (SplitChoice F))
    (hall : ∀ v ∈ candidateVertices M, P (candidateChoice M v) →
      candidateChoice M v ∈ all) :
    ((candidateVertices M).filter (fun v => P (candidateChoice M v))).card ≤
      2 * all.card := by
  let f : CandidateVertex F → Bool × SplitChoice F :=
    fun v => (v.1.2, candidateChoice M v)
  have h := Finset.card_le_card_of_injOn f
    (s := (candidateVertices M).filter (fun v => P (candidateChoice M v)))
    (t := (Finset.univ : Finset Bool) ×ˢ all)
    (fun v hv => by
      obtain ⟨hv, hp⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hall v hv hp⟩)
    (fun v _ w _ heq => by
      apply CandidateIncidence.eq_of_same_line_same_bit
      · exact congrArg (fun z : Bool × SplitChoice F => z.2.line) heq
      · exact congrArg (fun z : Bool × SplitChoice F => z.1) heq)
  simpa only [Finset.card_product, Finset.card_univ, Fintype.card_bool] using h

theorem slot_filter_card_le (M : MergedPairs F) (s : Slot F)
    (P : SplitChoice F → Prop) (all : Finset (SplitChoice F))
    (hall : ∀ v ∈ candidateSlot M s, P (candidateChoice M v) →
      candidateChoice M v ∈ all) :
    ((candidateSlot M s).filter (fun v => P (candidateChoice M v))).card ≤ all.card := by
  apply Finset.card_le_card_of_injOn (candidateChoice M)
  · intro v hv
    obtain ⟨hv, hp⟩ := Finset.mem_filter.mp hv
    exact hall v hv hp
  · intro v hv w hw heq
    apply candidateSlot_line_injective M s
      (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hw).1
    exact congrArg SplitChoice.line heq

theorem retained_test_card_le (M : MergedPairs F) (P : SplitChoice F → Prop) :
    ((candidateVertices M).filter (fun v => P (candidateChoice M v))).card ≤
      2 * (successfulTest M P).card := by
  apply retained_filter_card_le_two
  intro v hv hp
  exact Finset.mem_filter.mpr
    ⟨valid_mem_successfulChoices (CandidateIncidence.valid hv), hp⟩

theorem slot_test_card_le (M : MergedPairs F) (s : Slot F)
    (P : SplitChoice F → Prop) :
    ((candidateSlot M s).filter (fun v => P (candidateChoice M v))).card ≤
      (successfulTest M (fun C => C.line.1 = s.1 ∧ P C)).card := by
  apply slot_filter_card_le M s P (successfulTest M (fun C => C.line.1 = s.1 ∧ P C))
  intro v hv hp
  obtain ⟨hv, hs⟩ := mem_candidateSlot.mp hv
  apply (mem_successfulTest M _ _).mpr
  refine ⟨valid_mem_successfulChoices (retainedChoice_valid hv), ?_, hp⟩
  change v.1.1 = s.1
  exact congrArg (fun t : Slot F => t.1) hs

theorem pointCandidates_card_le (M : MergedPairs F) (p : Point F) :
    (CandidateIncidence.pointCandidates M p).card ≤
      2 * (successfulTest M (fun C => p ∈ designated M C)).card := by
  convert retained_test_card_le M (fun choice => p ∈ designated M choice) using 1
  congr 1
  unfold CandidateIncidence.pointCandidates
  congr 1

theorem pointLineCandidates_card_le (M : MergedPairs F) (p : Point F) (l : Line F) :
    (CandidateIncidence.pointLineCandidates M p l).card ≤
      2 * (successfulTest M (fun C => OnLine p C.line ∧
        ∃ r ∈ designated M C, OnLine r l)).card := by
  convert retained_test_card_le M (fun choice => OnLine p choice.line ∧
    ∃ point ∈ designated M choice, OnLine point l) using 1
  congr 1
  unfold CandidateIncidence.pointLineCandidates
  congr 1

theorem twoLineCandidates_card_le (M : MergedPairs F) (l k : Line F) :
    (CandidateIncidence.twoLineCandidates M l k).card ≤
      2 * (successfulTest M (fun C =>
        ∃ p ∈ designated M C, ∃ r ∈ designated M C,
          p ≠ r ∧ OnLine p l ∧ OnLine r k)).card := by
  convert retained_test_card_le M (fun choice =>
    ∃ point ∈ designated M choice, ∃ other ∈ designated M choice,
      point ≠ other ∧ OnLine point l ∧ OnLine other k) using 1
  congr 1
  unfold CandidateIncidence.twoLineCandidates
  congr 1

theorem generatorPairCandidates_card_le (M : MergedPairs F)
    (e : Finset (Direction F)) :
    (CandidateIncidence.generatorPairCandidates M e).card ≤
      2 * (successfulTest M (fun C => e ⊆ generatorSet C.tuple)).card := by
  convert retained_test_card_le M (fun choice => e ⊆ generatorSet choice.tuple) using 1
  congr 1
  unfold CandidateIncidence.generatorPairCandidates
  congr 1

theorem lineHitSlot_card_le (M : MergedPairs F) (s : Slot F) (l : Line F) :
    (CandidateIncidence.lineHitSlot M s l).card ≤
      (successfulTest M (fun C => C.line.1 = s.1 ∧
        ∃ p ∈ designated M C, OnLine p l)).card := by
  convert slot_test_card_le M s
    (fun choice => ∃ point ∈ designated M choice, OnLine point l) using 1
  congr 1
  unfold CandidateIncidence.lineHitSlot
  congr 1

theorem lineHitAll_card_le (M : MergedPairs F) (l : Line F) :
    ((candidateVertices M).filter (fun v =>
      ∃ p ∈ CandidateIncidence.points M v, OnLine p l)).card ≤
      2 * (successfulTest M (fun C => ∃ p ∈ designated M C, OnLine p l)).card := by
  convert retained_test_card_le M
    (fun choice => ∃ point ∈ designated M choice, OnLine point l) using 1
  congr 1
  congr 1

end
end Balanced.CandidateRetentionTransport

end OAI
