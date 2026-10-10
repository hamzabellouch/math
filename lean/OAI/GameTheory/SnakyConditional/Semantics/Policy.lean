import OAI.GameTheory.SnakyConditional.Model

namespace OAI

namespace SnakyConditional.OrdinaryStrategy
variable {α : Type*} [DecidableEq α] [Infinite α]
def GoodMove (win : Finset α → Prop) (nextBudget : ℕ)
    (M B : Finset α) (x : α) : Prop :=
  x ∉ M ∧ x ∉ B ∧ ∀ b, b ∉ insert x M → b ∉ B →
    WinsIn win nextBudget (insert x M) (insert b B)
omit [Infinite α] in
theorem winsIn_zero_iff {win : Finset α → Prop} {M B : Finset α} :
    WinsIn win 0 M B ↔ win M := by
  constructor
  · intro h; cases h with | done hw => exact hw
  · exact WinsIn.done
theorem exists_good_move {win : Finset α → Prop}
    (hmono : ∀ M N, M ⊆ N → win M → win N)
    {n : ℕ} {M B : Finset α} (h : WinsIn win (n + 1) M B) :
    ∃ x, GoodMove win n M B x := by
  cases h with
  | done hw =>
      obtain ⟨x, hx⟩ := (M ∪ B).exists_notMem
      refine ⟨x, ?_, ?_, ?_⟩
      · exact fun hxM => hx (Finset.mem_union_left B hxM)
      · exact fun hxB => hx (Finset.mem_union_right M hxB)
      · intro b _ _
        exact WinsIn.done (hmono M (insert x M) (Finset.subset_insert x M) hw)
  | move x hxM hxB next => exact ⟨x, hxM, hxB, next⟩
noncomputable def policy (win : Finset α → Prop) (r : ℕ) (M B : Finset α) : α := by
  classical
  exact if h : ∃ x, GoodMove win (r - 1) M B x then Classical.choose h
    else Classical.choose ((M ∪ B).exists_notMem)
theorem policy_fresh (win : Finset α → Prop) (r : ℕ) (M B : Finset α) :
    policy win r M B ∉ M ∧ policy win r M B ∉ B := by
  classical
  unfold policy
  split_ifs with h
  · exact ⟨(Classical.choose_spec h).1, (Classical.choose_spec h).2.1⟩
  · have hx := Classical.choose_spec ((M ∪ B).exists_notMem)
    exact ⟨fun hxM => hx (Finset.mem_union_left B hxM),
      fun hxB => hx (Finset.mem_union_right M hxB)⟩
theorem policy_good {win : Finset α → Prop}
    (hmono : ∀ M N, M ⊆ N → win M → win N)
    {n : ℕ} {M B : Finset α} (h : WinsIn win (n + 1) M B) :
    GoodMove win n M B (policy win (n + 1) M B) := by
  classical
  have hex := exists_good_move hmono h
  unfold policy
  simp only [Nat.add_sub_cancel]
  rw [dite_eq_left hex]
  exact Classical.choose_spec hex
theorem policy_last_move_wins {win : Finset α → Prop}
    (hmono : ∀ M N, M ⊆ N → win M → win N)
    {M B : Finset α} (h : WinsIn win 1 M B) :
    win (insert (policy win 1 M B) M) := by
  have hg := policy_good hmono h
  obtain ⟨b, hb⟩ := ((insert (policy win 1 M B) M) ∪ B).exists_notMem
  apply winsIn_zero_iff.mp
  exact hg.2.2 b
    (fun hbM => hb (Finset.mem_union_left B hbM))
    (fun hbB => hb (Finset.mem_union_right _ hbB))
abbrev Policy (α : Type*) := ℕ → Finset α → Finset α → α
def playState (σ : Policy α) (N : ℕ) (β : ℕ → α) (M₀ B₀ : Finset α) :
    ℕ → Finset α × Finset α
  | 0 => (M₀, B₀)
  | k + 1 =>
      let state := playState σ N β M₀ B₀ k
      (insert (σ (N - k) state.1 state.2) state.1, insert (β k) state.2)
def makerAt (σ : Policy α) (N : ℕ) (β : ℕ → α) (M₀ B₀ : Finset α) (k : ℕ) : α :=
  let state := playState σ N β M₀ B₀ k
  σ (N - k) state.1 state.2
def LegalRepliesBeforeFinal (σ : Policy α) (N : ℕ) (β : ℕ → α)
    (M₀ B₀ : Finset α) : Prop :=
  ∀ k, k + 1 < N →
    β k ∉ insert (makerAt σ N β M₀ B₀ k) (playState σ N β M₀ B₀ k).1 ∧
    β k ∉ (playState σ N β M₀ B₀ k).2
omit [Infinite α] in
theorem disjoint_after_round {M B : Finset α} {x b : α}
    (hMB : Disjoint M B) (hxB : x ∉ B) (hbM : b ∉ insert x M) :
    Disjoint (insert x M) (insert b B) := by
  refine Finset.disjoint_left.mpr ?_
  intro y hyM hyB
  rcases Finset.mem_insert.mp hyM with rfl | hyM
  · rcases Finset.mem_insert.mp hyB with rfl | hx
    · exact hbM (Finset.mem_insert_self _ _)
    · exact hxB hx
  · rcases Finset.mem_insert.mp hyB with rfl | hyB
    · exact hbM (Finset.mem_insert_of_mem hyM)
    · exact Finset.disjoint_left.mp hMB hyM hyB
omit [Infinite α] in
theorem playState_maker_card (σ : Policy α)
    (hfresh : ∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B)
    (N : ℕ) (β : ℕ → α) (M₀ B₀ : Finset α) :
    ∀ k, (playState σ N β M₀ B₀ k).1.card = M₀.card + k := by
  intro k
  induction k with
  | zero => simp [playState]
  | succ k ih =>
      change (insert (σ (N - k) (playState σ N β M₀ B₀ k).1
        (playState σ N β M₀ B₀ k).2) (playState σ N β M₀ B₀ k).1).card = _
      rw [Finset.card_insert_of_notMem (hfresh _ _ _).1, ih]
      omega
omit [Infinite α] in
theorem playState_legal_prefix (σ : Policy α)
    (hfresh : ∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B)
    (N : ℕ) (β : ℕ → α) (M₀ B₀ : Finset α)
    (h₀ : Disjoint M₀ B₀) (hβ : LegalRepliesBeforeFinal σ N β M₀ B₀) :
    ∀ k, k < N → Disjoint (playState σ N β M₀ B₀ k).1
        (playState σ N β M₀ B₀ k).2 ∧
      (playState σ N β M₀ B₀ k).2.card = B₀.card + k := by
  intro k
  induction k with
  | zero => intro _; exact ⟨h₀, by simp [playState]⟩
  | succ k ih =>
      intro hk
      obtain ⟨hi, hc⟩ := ih (by omega)
      obtain ⟨hbM, hbB⟩ := hβ k hk
      constructor
      · exact disjoint_after_round hi (hfresh _ _ _).2 hbM
      · change (insert (β k) (playState σ N β M₀ B₀ k).2).card = _
        rw [Finset.card_insert_of_notMem hbB, hc]
        omega
omit [Infinite α] in
                                                                        
                                                                          
theorem final_maker_disjoint (σ : Policy α)
    (hfresh : ∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B)
    (n : ℕ) (β : ℕ → α) (M₀ B₀ : Finset α)
    (h₀ : Disjoint M₀ B₀) (hβ : LegalRepliesBeforeFinal σ (n + 1) β M₀ B₀) :
    Disjoint (playState σ (n + 1) β M₀ B₀ (n + 1)).1
      (playState σ (n + 1) β M₀ B₀ n).2 := by
  have hi := (playState_legal_prefix σ hfresh (n + 1) β M₀ B₀ h₀ hβ n (by omega)).1
  change Disjoint (insert (σ ((n + 1) - n) (playState σ (n + 1) β M₀ B₀ n).1
    (playState σ (n + 1) β M₀ B₀ n).2) (playState σ (n + 1) β M₀ B₀ n).1)
    (playState σ (n + 1) β M₀ B₀ n).2
  exact Finset.disjoint_insert_left.mpr ⟨(hfresh _ _ _).2, hi⟩
theorem policy_wins_round_invariant {win : Finset α → Prop}
    (hmono : ∀ M N, M ⊆ N → win M → win N)
    (N : ℕ) (β : ℕ → α) (M₀ B₀ : Finset α)
    (hstart : WinsIn win N M₀ B₀)
    (hβ : LegalRepliesBeforeFinal (policy win) N β M₀ B₀) :
    ∀ k, k < N → WinsIn win (N - k)
      (playState (policy win) N β M₀ B₀ k).1
      (playState (policy win) N β M₀ B₀ k).2 := by
  intro k
  induction k with
  | zero => intro _; simpa [playState] using hstart
  | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hbudget : N - k = (N - (k + 1)) + 1 := by omega
      rw [hbudget] at ih'
      have hg := policy_good hmono ih'
      obtain ⟨hbM, hbB⟩ := hβ k hk
      have hstep := hg.2.2 (β k)
      have hx : policy win ((N - (k + 1)) + 1)
          (playState (policy win) N β M₀ B₀ k).1
          (playState (policy win) N β M₀ B₀ k).2 =
          makerAt (policy win) N β M₀ B₀ k := by
        simp only [makerAt, hbudget]
      rw [hx] at hstep
      simpa only [playState, makerAt] using hstep hbM hbB
theorem policy_wins {win : Finset α → Prop}
    (hmono : ∀ M N, M ⊆ N → win M → win N)
    (N : ℕ) (β : ℕ → α) (M₀ B₀ : Finset α)
    (hstart : WinsIn win N M₀ B₀)
    (hβ : LegalRepliesBeforeFinal (policy win) N β M₀ B₀) :
    win (playState (policy win) N β M₀ B₀ N).1 := by
  cases N with
  | zero => exact winsIn_zero_iff.mp hstart
  | succ n =>
      have hi := policy_wins_round_invariant hmono (n + 1) β M₀ B₀ hstart hβ n (by omega)
      have hi' : WinsIn win 1 (playState (policy win) (n + 1) β M₀ B₀ n).1
          (playState (policy win) (n + 1) β M₀ B₀ n).2 := by simpa using hi
      have hw := policy_last_move_wins hmono hi'
      simpa [playState] using hw
theorem winsIn_has_ordinary_policy {win : Finset α → Prop}
    (hmono : ∀ M N, M ⊆ N → win M → win N)
    {N : ℕ} {M₀ B₀ : Finset α} (hstart : WinsIn win N M₀ B₀) :
    ∃ σ : Policy α,
      (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β, LegalRepliesBeforeFinal σ N β M₀ B₀ →
        win (playState σ N β M₀ B₀ N).1 := by
  refine ⟨policy win, policy_fresh win, ?_⟩
  intro β hβ
  exact policy_wins hmono N β M₀ B₀ hstart hβ
end SnakyConditional.OrdinaryStrategy

end OAI
