import OAI.Combinatorics.LowSpaceSubsetSum.Counting.ParentLiveState

namespace OAI

/-! # Uniform payload bounds for all concrete parent states

The estimates use the stored type invariants, so an interrupted join and an
already overflowing dictionary satisfy the same bounds as a completed run.
Shared input arrays are counted once outside the mutable state.
-/

namespace LowSpaceSubsetSum.ParentLiveBounds

variable {n : ℕ}

theorem reader_le (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (s : CountedParentJoin.State I F P mode right d)
    (C : ℕ) (ht : 2 ^ (d + 1) ≤ 4 * (C + 1)) :
    ParentLiveState.reader s ≤ 176 * inputScale I * (C + 1) := by
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hc : 12 * n + 32 ≤ 44 * inputScale I := by omega
  have hm := Nat.mul_le_mul hc ht
  rw [ParentLiveState.reader_exact]
  nlinarith only [hm]

theorem frame_le (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C : ℕ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (st : StreamJoin.State (CountedParentJoin.State I F P .direct right₁ d₁)
      (CountedParentJoin.State I F P (.complementary t) right₂ d₂) (StoredEntry.Dictionary I C))
    (h₁ : 2 ^ (d₁ + 1) ≤ 4 * (C + 1)) (h₂ : 2 ^ (d₂ + 1) ≤ 4 * (C + 1)) :
    ParentLiveState.frame st ≤ 400 * inputScale I * (C + 1) := by
  have hl := reader_le I F P .direct right₁ st.left C h₁
  have hr := reader_le I F P (.complementary t) right₂ st.right C h₂
  have hd := ParentLiveState.dictionary_scale I C st.user
  have hu : 1 ≤ inputScale I := by unfold inputScale; omega
  have hm : inputScale I ≤ inputScale I * (C + 1) := by nlinarith only [hu]
  unfold ParentLiveState.frame
  nlinarith only [hl, hr, hd, hu, hm]

theorem shared_le (I : Instance n) (C : ℕ) (left right : Array (LeafRecord n))
    (hl : left.size ≤ C) (hr : right.size ≤ C) :
    ParentLiveState.sharedArrays left right ≤ 8 * inputScale I * (C + 1) := by
  have h := ParentLiveState.sharedArrays_le left right C hl hr
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hc : 3 * n + 4 ≤ 4 * inputScale I := by omega
  have hm := Nat.mul_le_mul hc (by omega : 2 * C + 1 ≤ 2 * (C + 1))
  exact h.trans (by nlinarith only [hm])

theorem all_inputs_and_state (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C : ℕ)
    (left₁ right₁ left₂ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (st : StreamJoin.State (CountedParentJoin.State I F P .direct right₁ d₁)
      (CountedParentJoin.State I F P (.complementary t) right₂ d₂) (StoredEntry.Dictionary I C))
    (h₁ : 2 ^ (d₁ + 1) ≤ 4 * (C + 1)) (h₂ : 2 ^ (d₂ + 1) ≤ 4 * (C + 1))
    (hl₁ : left₁.size ≤ C) (hr₁ : right₁.size ≤ C) (hl₂ : left₂.size ≤ C) (hr₂ : right₂.size ≤ C)
    (hn : 10000 ≤ n) :
    ParentLiveState.frame st + ParentLiveState.sharedArrays left₁ right₁ +
      ParentLiveState.sharedArrays left₂ right₂ ≤ inputScale I ^ 2 * (C + 1) := by
  have hs := frame_le I F P t C right₁ right₂ st h₁ h₂
  have ha := shared_le I C left₁ right₁ hl₁ hr₁
  have hb := shared_le I C left₂ right₂ hl₂ hr₂
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hc : 416 * inputScale I ≤ inputScale I ^ 2 := by nlinarith only [hu, hn]
  have hm := Nat.mul_le_mul_right (C + 1) hc
  nlinarith only [hs, ha, hb, hm]

end LowSpaceSubsetSum.ParentLiveBounds

end OAI
