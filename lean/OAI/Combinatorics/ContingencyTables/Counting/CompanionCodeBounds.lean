import OAI.Combinatorics.ContingencyTables.Counting.CompanionOuterPhaseProgram

namespace OAI

/-! # Encoded profile bounds independent of learned multiplier sizes -/
namespace ContingencyTables.CompanionCodeBounds
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma restart_next (i : ℕ) (s : CompanionRestartProgram.State) :
    weight (CompanionRestartProgram.next (i,s)) ≤ 6*s.1.1.2.length+1 := by
  simpa only [CompanionRestartProgram.next,CompanionRestartProgram.bound,Nat.size_one, Nat.reduceMul,Nat.reduceAdd,Nat.mul_comm] using
    ProfilePrograms.capView_weight s.1.1.2.length 1 (CompanionRestartProgram.candidate (i,s))

lemma restart_fold (is : List ℕ) (s : CompanionRestartProgram.State) :
    weight ((is.foldl (fun s i => CompanionRestartProgram.advance (i,s)) s).2) ≤
      max (weight s.2) (6*s.1.1.2.length+1) := by
  induction is using List.reverseRecOn with
  | nil => exact le_max_left _ _
  | append_singleton is i _ =>
    rw [List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil]
    apply (restart_next _ _).trans
    rw [CompanionRestartProgram.fold_fixed]
    exact le_max_right _ _

lemma restart_output (z : CompanionRestartProgram.Input) :
    weight (CompanionRestartProgram.output z) ≤ 7*weight z.1.2+1 := by
  have h := restart_fold (CompanionRestartProgram.indices z) (z,z.1.2)
  change weight (CompanionRestartProgram.output z) ≤ _ at h
  dsimp only at h
  have hl := list_length_le_weight z.1.2
  exact h.trans (max_le (by omega) (by omega))

lemma initialized_output (z : CompanionInitializedRestartProgram.Input) :
    weight (CompanionInitializedRestartProgram.output z) ≤
      7*weight (CompanionInitializedRestartProgram.initialCode z)+1 :=
  restart_output (CompanionInitializedRestartProgram.prepare z)

lemma walk_next (bits : List Bool) (s : CompanionBoundedWalkProgram.State) :
    weight (CompanionBoundedWalkProgram.next (bits,s)) ≤ 6*s.1.2.length+1 := by
  simpa only [CompanionBoundedWalkProgram.next,CompanionBoundedWalkProgram.bound,Nat.size_one,Nat.reduceMul,Nat.reduceAdd,Nat.mul_comm] using
    ProfilePrograms.capView_weight s.1.2.length 1 (CompanionBoundedWalkProgram.candidate (bits,s))

lemma record_bound (words : List (List Bool)) (s : CompanionBoundedWalkProgram.RecordState)
    (B : ℕ) (hc : weight s.1.2 ≤ B) (hf : 6*s.1.1.2.length+1 ≤ B)
    (hh : ∀ code∈s.2,weight code ≤ B) :
    let out := words.foldl (fun s bits => CompanionBoundedWalkProgram.recordAdvance (bits,s)) s
    (∀ code∈out.2,weight code ≤ B) ∧ out.2.length=s.2.length+words.length := by
  induction words generalizing s with
  | nil => exact ⟨hh,by simp⟩
  | cons word words ih =>
    have hn := (walk_next word s.1).trans hf
    have h := ih (CompanionBoundedWalkProgram.recordAdvance (word,s)) hn hf (by
      intro code hcode
      rcases List.mem_cons.mp hcode with he | he
      · subst code; exact hn
      · exact hh code he)
    exact ⟨h.1,by simpa only [List.foldl_cons,CompanionBoundedWalkProgram.recordAdvance,
      List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.2⟩

lemma history_bound (s : CompanionBoundedWalkProgram.State) (words : List (List Bool))
    (B : ℕ) (hc : weight s.2 ≤ B) (hf : 6*s.1.2.length+1 ≤ B) :
    (∀ code∈CompanionBoundedWalkProgram.history (s,words),weight code ≤ B) ∧
      (CompanionBoundedWalkProgram.history (s,words)).length=words.length+1 := by
  have h := record_bound words (s,[s.2]) B hc hf (by simpa only [List.mem_singleton] using
    fun code he => he ▸ hc)
  constructor
  · intro code hcode
    exact h.1 code (List.mem_reverse.mp hcode)
  · simpa only [CompanionBoundedWalkProgram.history,CompanionBoundedWalkProgram.recordWalk,
      CompanionBoundedWalkProgram.initialRecord,List.length_reverse,List.length_cons,List.length_nil,
      Nat.add_comm] using h.2

lemma trajectory_length (z : CompanionTrajectoryProgram.Input) :
    (CompanionTrajectoryProgram.output z).length ≤ z.2.length+1 := by
  let s := z.1.1
  let words := CompanionFlatReturnProgram.words z
  have h := history_bound s words (weight s.2+6*s.1.2.length+1) (by omega) (by omega)
  have hlen : (CompanionTrajectoryProgram.output z).length=words.length+1 := h.2
  have hl : words.length ≤ z.2.length := by
    unfold words CompanionFlatReturnProgram.words DensePrograms.wordChunks DensePrograms.completeWordRows
    simp only [List.length_take,List.length_map,List.length_range]
    exact (min_le_right _ _).trans (Nat.div_le_self _ _)
  omega

lemma trajectory_codes (z : CompanionTrajectoryProgram.Input) (B : ℕ)
    (hc : weight z.1.1.2 ≤ B) (hf : 6*z.1.1.1.2.length+1 ≤ B) :
    ∀ code∈CompanionTrajectoryProgram.output z,weight code ≤ B :=
  (history_bound z.1.1 (CompanionFlatReturnProgram.words z) B hc hf).1

end ContingencyTables.CompanionCodeBounds

end OAI
