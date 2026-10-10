import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Candidates.Candidates

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

@[simp] theorem retainedChoice_line (M : MergedPairs F) (l : Line F) :
    (retainedChoice M l).line = l := rfl

theorem retainedChoice_valid {M : MergedPairs F} {l : Line F}
    (h : SupportsValidTuple M l) : ValidChoice M l.1 (retainedChoice M l) := by
  simpa only [retainedChoice, dite_eq_left h] using Classical.choose_spec h

theorem choicesCompatible_symm {M : MergedPairs F} {g h : Direction F}
    {A B : SplitChoice F} (hc : ChoicesCompatible M g h A B) :
    ChoicesCompatible M h g B A := by
  rcases hc with ⟨hab, hba, hgen, hmerged⟩
  refine ⟨hba, hab, ?_, ?_⟩
  · simpa only [Finset.inter_comm] using hgen
  · intro heq d
    exact ⟨(hmerged heq.symm d).2, (hmerged heq.symm d).1⟩

theorem candidateAdjacent_symm {M : MergedPairs F} {v w : CandidateVertex F}
    (h : CandidateAdjacent M v w) : CandidateAdjacent M w v := by
  rcases h with ⟨hv, hw, hne, hbad⟩
  exact ⟨hw, hv, Ne.symm hne, fun hgood => hbad (choicesCompatible_symm hgood)⟩

theorem candidateAdjacent_irrefl (M : MergedPairs F) (v : CandidateVertex F) :
    ¬ CandidateAdjacent M v v := by
  intro h
  exact h.2.2.1 rfl

@[simp] theorem mem_candidateVertices {M : MergedPairs F} {v : CandidateVertex F} :
    v ∈ candidateVertices M ↔ SupportsValidTuple M (candidateLine v) := by
  simp [candidateVertices]

@[simp] theorem mem_candidateSlot {M : MergedPairs F} {s : Slot F} {v : CandidateVertex F} :
    v ∈ candidateSlot M s ↔ SupportsValidTuple M (candidateLine v) ∧ v.1 = s := by
  simp [candidateSlot]

theorem candidateSlot_offset_injective (M : MergedPairs F) (s : Slot F) :
    Set.InjOn (fun v : CandidateVertex F => v.2) (candidateSlot M s) := by
  intro v hv w hw hoff
  apply Prod.ext
  · exact (mem_candidateSlot.mp hv).2.trans (mem_candidateSlot.mp hw).2.symm
  · exact hoff

theorem candidateSlot_card_le (M : MergedPairs F) (s : Slot F) :
    (candidateSlot M s).card ≤ Fintype.card F := by
  calc
    (candidateSlot M s).card ≤ (Finset.univ : Finset F).card :=
      Finset.card_le_card_of_injOn (fun v : CandidateVertex F => v.2)
        (fun _ _ => Finset.mem_univ _) (candidateSlot_offset_injective M s)
    _ = Fintype.card F := Finset.card_univ

theorem candidateSlot_line_injective (M : MergedPairs F) (s : Slot F) :
    Set.InjOn (candidateLine (F := F)) (candidateSlot M s : Set (CandidateVertex F)) := by
  intro v hv w hw heq
  have hoff : v.2 = w.2 := congrArg (fun l : Line F => l.2) heq
  exact candidateSlot_offset_injective M s hv hw hoff

theorem Configuration.compatible_iff_pairwise (C : Configuration F) :
    C.Compatible ↔ ∀ s t, s ≠ t →
      ChoicesCompatible C.merged s.1 t.1 (C.choice s) (C.choice t) := by
  constructor
  · rintro ⟨hpoints, hgen, hmerged⟩ s t hst
    refine ⟨hpoints t s (Ne.symm hst), hpoints s t hst, hgen s t hst, ?_⟩
    intro heq d
    exact ⟨hmerged s t hst heq d, hmerged t s (Ne.symm hst) heq.symm d⟩
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro s t hst
      exact (h s t hst).2.1
    · intro s t hst
      exact (h s t hst).2.2.1
    · intro s t hst heq d
      exact ((h s t hst).2.2.2 heq d).1

theorem selectedConfiguration_valid {M : MergedPairs F} {f : Slot F → F}
    (hd : DistinctConstituents M) (hf : CandidateSelector M f) :
    (selectedConfiguration M f).Valid := by
  refine ⟨hd, ?_⟩
  intro s
  exact retainedChoice_valid (hf s)

theorem selectedConfiguration_compatible_iff {M : MergedPairs F} {f : Slot F → F}
    (hf : CandidateSelector M f) :
    (selectedConfiguration M f).Compatible ↔ IndependentSelector M f := by
  rw [Configuration.compatible_iff_pairwise]
  constructor
  · intro h s t hst hadj
    exact hadj.2.2.2 (h s t hst)
  · intro h s t hst
    by_contra hbad
    apply h s t hst
    exact ⟨mem_candidateVertices.mpr (hf s), mem_candidateVertices.mpr (hf t), hst, hbad⟩

end
end Balanced

end OAI
