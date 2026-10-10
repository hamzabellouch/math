import OAI.GameTheory.SnakyTwentyOne.Model

namespace OAI

namespace SnakyPrototype.OrdinaryStrategy
variable {α : Type*} [DecidableEq α] [Infinite α]
noncomputable def freshReply (M B : Finset α) : α :=
  Classical.choose ((M ∪ B).exists_notMem)
theorem freshReply_not_owned (M B : Finset α) :
    freshReply M B ∉ M ∧ freshReply M B ∉ B := by
  have h := Classical.choose_spec ((M ∪ B).exists_notMem)
  exact ⟨fun hM => h (Finset.mem_union_left B hM),
    fun hB => h (Finset.mem_union_right M hB)⟩
noncomputable def freshReplyState (σ : Policy α) (N : ℕ) (M₀ B₀ : Finset α) :
    ℕ → Finset α × Finset α
  | 0 => (M₀, B₀)
  | k + 1 =>
      let state := freshReplyState σ N M₀ B₀ k
      let M' := insert (σ (N - k) state.1 state.2) state.1
      (M', insert (freshReply M' state.2) state.2)
noncomputable def freshReplies (σ : Policy α) (N : ℕ) (M₀ B₀ : Finset α)
    (k : ℕ) : α :=
  let state := freshReplyState σ N M₀ B₀ k
  freshReply (insert (σ (N - k) state.1 state.2) state.1) state.2
theorem playState_freshReplies (σ : Policy α) (N : ℕ) (M₀ B₀ : Finset α) (k : ℕ) :
    playState σ N (freshReplies σ N M₀ B₀) M₀ B₀ k =
      freshReplyState σ N M₀ B₀ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [playState, freshReplyState, ih, freshReplies]
theorem exists_legal_replies (σ : Policy α) (N : ℕ) (M₀ B₀ : Finset α) :
    ∃ β, LegalRepliesBeforeFinal σ N β M₀ B₀ := by
  refine ⟨freshReplies σ N M₀ B₀, ?_⟩
  intro k _
  simp only [makerAt, playState_freshReplies, freshReplies]
  exact freshReply_not_owned _ _
end SnakyPrototype.OrdinaryStrategy

end OAI
