import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationGroupCells

namespace OAI

/-! # A stopped parent-join step with its live-cell trace

The two fetched records and replacement reader states remain live while a
matching tie group is processed. Shared leaf arrays stay outside this frame.
-/

namespace LowSpaceSubsetSum.RepresentationStepCells

variable {n : ℕ}

abbrev State (I : Instance n) (F : IndexedMask n) (P t : ℤ)
    (right₁ right₂ : Array (LeafRecord n)) (d₁ d₂ C : ℕ) :=
  StreamJoin.State (RepresentationGroupCells.Left I F P right₁ d₁)
    (RepresentationGroupCells.Right I F P t right₂ d₂) (StoredEntry.Dictionary I C)

def run (I : Instance n) (F : IndexedMask n) (P t : ℤ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (C base front fill outer inner copy B fuel₁ fuel₂ : ℕ)
    (st : State I F P t right₁ right₂ d₁ d₂ C) (budget : ℕ) :
    (Option (State I F P t right₁ right₂ d₁ d₂ C × ℕ) × ℕ) × ℕ :=
  let retained := ParentLiveState.frame st + 32
  if base ≤ budget then
    if st.done then ((some (st, budget - base), 1), retained) else
    let x := RepresentationReaderCells.read I F P .direct right₁ st.left
    let firstPeak := retained + x.2 + 16
    match x.1.1 with
    | none => ((some ({st with queries := st.queries + 1, done := true}, budget - base), x.1.2 + 4), firstPeak)
    | some (a, left) =>
      let y := RepresentationReaderCells.read I F P (.complementary t) right₂ st.right
      let secondPeak := max firstPeak (retained + ParentLiveState.reader left +
        CountedParentJoin.cells a + y.2 + 16)
      match y.1.1 with
      | none => ((some ({st with queries := st.queries + 2, done := true}, budget - base), x.1.2 + y.1.2 + 5), secondPeak)
      | some (b, right) =>
        let k₁ := RepresentationKeyCells.pairKey I F P .direct a
        let k₂ := RepresentationKeyCells.pairKey I F P (.complementary t) b
        let live := retained + ParentLiveState.reader left + ParentLiveState.reader right +
          CountedParentJoin.cells a + CountedParentJoin.cells b + 64
        let peak := max secondPeak (live + k₁.2 + k₂.2)
        if k₁.1.1 < k₂.1.1 then
          ((some ({st with left := left, queries := st.queries + 2}, budget - base),
            x.1.2 + y.1.2 + k₁.1.2 + k₂.1.2 + 8), peak)
        else if k₂.1.1 < k₁.1.1 then
          ((some ({st with right := right, queries := st.queries + 2}, budget - base),
            x.1.2 + y.1.2 + k₁.1.2 + k₂.1.2 + 8), peak)
        else
          let out := RepresentationGroupCells.run I F P t right₁ right₂ C front fill outer inner copy
            k₁.1.1 B fuel₁ fuel₂ st.left st.right st.user (budget - base)
          ((out.1.1.map (fun (group, remaining) => (BudgetedStreamStep.advance st group, remaining)),
            x.1.2 + y.1.2 + k₁.1.2 + k₂.1.2 + out.1.2 + 16), max peak (live + out.2))
  else ((none, 1), retained)

theorem run_value (I : Instance n) (F : IndexedMask n) (P t : ℤ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (C base front fill outer inner copy B fuel₁ fuel₂ : ℕ)
    (st : State I F P t right₁ right₂ d₁ d₂ C) (budget : ℕ) :
    (run I F P t right₁ right₂ C base front fill outer inner copy B fuel₁ fuel₂ st budget).1 =
      BudgetedStreamStep.execute base front fill outer inner copy
        (RepresentationKeys.read I F P .direct right₁) (RepresentationKeys.pairKey I F P .direct)
        (RepresentationKeys.read I F P (.complementary t) right₂)
        (RepresentationKeys.pairKey I F P (.complementary t)) CountedParentJoin.cells
        (StoredEntry.report I C (CountedRepresentationEmit.emit I F))
        (CountedParentJoin.snapshot I F P (.complementary t) right₂) B fuel₁ fuel₂ st budget := by
  unfold run BudgetedStreamStep.execute
  dsimp only
  split
  · split
    · rfl
    · simp only [RepresentationReaderCells.read_value]
      cases hx : (RepresentationKeys.read I F P .direct right₁ st.left).1 with
      | none => rfl
      | some p =>
        rcases p with ⟨a, left⟩
        dsimp only
        cases hy : (RepresentationKeys.read I F P (.complementary t) right₂ st.right).1 with
        | none => rfl
        | some p =>
          rcases p with ⟨b, right⟩
          dsimp only
          simp only [RepresentationKeyCells.pairKey_value, RepresentationGroupCells.run_value]
          split
          · rfl
          · split <;> rfl
  · rfl

theorem run_cells (I : Instance n) (F : IndexedMask n) (P t : ℤ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (C base front fill outer inner copy B fuel₁ fuel₂ : ℕ)
    (st : State I F P t right₁ right₂ d₁ d₂ C) (budget : ℕ) (hn : 10000 ≤ n)
    (hd₁ : d₁ ≤ n) (hd₂ : d₂ ≤ n)
    (ht₁ : 2 ^ (d₁ + 1) ≤ 4 * (C + 1)) (ht₂ : 2 ^ (d₂ + 1) ≤ 4 * (C + 1)) (hB : B ≤ C) :
    (run I F P t right₁ right₂ C base front fill outer inner copy B fuel₁ fuel₂ st budget).2 ≤
      inputScale I ^ 10 * (C + 1) := by
  let u := inputScale I
  let H := u ^ 9 * (C + 1)
  have hu : n + 1 ≤ u := by unfold u inputScale; omega
  have hp : 1 ≤ u := by omega
  have hscale : 1000 * u ≤ u ^ 9 := by
    have h : u ≤ u ^ 8 := by
      simpa only [pow_one] using Nat.pow_le_pow_right hp (by decide : 1 ≤ 8)
    have hm := Nat.mul_le_mul_right u (show 1000 ≤ u ^ 8 by omega)
    simpa only [pow_succ] using hm
  have hs : 1000 * u * (C + 1) ≤ H := Nat.mul_le_mul_right (C + 1) hscale
  have hup : 1 ≤ u * (C + 1) := Nat.mul_pos hp (by omega)
  have h64 : 64 ≤ H := by nlinarith only [hs, hup]
  have hf := ParentLiveBounds.frame_le I F P t C right₁ right₂ st ht₁ ht₂
  have hret : ParentLiveState.frame st + 32 ≤ H := by
    change _ ≤ 400 * u * (C + 1) at hf
    nlinarith only [hf, hs, hup]
  have hreader₁ : ∀ s : RepresentationGroupCells.Left I F P right₁ d₁, ParentLiveState.reader s ≤ H := by
    intro s
    have h := ParentLiveBounds.reader_le I F P .direct right₁ s C ht₁
    change _ ≤ 176 * u * (C + 1) at h
    nlinarith only [h, hs, hup]
  have hreader₂ : ∀ s : RepresentationGroupCells.Right I F P t right₂ d₂, ParentLiveState.reader s ≤ H := by
    intro s
    have h := ParentLiveBounds.reader_le I F P (.complementary t) right₂ s C ht₂
    change _ ≤ 176 * u * (C + 1) at h
    nlinarith only [h, hs, hup]
  have hpow : u ^ 4 * (C + 1) ≤ H :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp (by decide : 4 ≤ 9))
  have hr₁ := (RepresentationReaderCells.read_scale I F P .direct right₁ st.left C hn hd₁ ht₁).trans hpow
  have hr₂ := (RepresentationReaderCells.read_scale I F P (.complementary t) right₂ st.right C hn hd₂ ht₂).trans hpow
  have hrecord : ∀ x : LeafRecord n × LeafRecord n, CountedParentJoin.cells x ≤ H := by
    intro x
    have h := CountedParentJoin.cells_le x
    nlinarith only [h, hs, hu, hup]
  have hkey : ∀ mode x, (RepresentationKeyCells.pairKey I F P mode x).2 ≤ H := by
    intro mode x
    have h := RepresentationKeyCells.pairKey_cells I F P mode x
    nlinarith only [h, hs, hu, hup]
  have hpeak : (run I F P t right₁ right₂ C base front fill outer inner copy B fuel₁ fuel₂ st budget).2 ≤ 16 * H := by
    unfold run
    dsimp only
    split
    · split
      · dsimp only; omega
      · cases hx : (RepresentationReaderCells.read I F P .direct right₁ st.left).1.1 with
        | none => dsimp only; omega
        | some p =>
          rcases p with ⟨a, left⟩
          have hleft := hreader₁ left
          have ha := hrecord a
          dsimp only
          cases hy : (RepresentationReaderCells.read I F P (.complementary t) right₂ st.right).1.1 with
          | none => dsimp only; omega
          | some p =>
            rcases p with ⟨b, right⟩
            have hright := hreader₂ right
            have hb := hrecord b
            have hk₁ := hkey .direct a
            have hk₂ := hkey (.complementary t) b
            have hg := RepresentationGroupCells.run_cells I F P t right₁ right₂ C front fill outer inner copy
              (RepresentationKeyCells.pairKey I F P .direct a).1.1 B fuel₁ fuel₂ st.left st.right st.user
              (budget - base) hn hd₁ hd₂ ht₁ ht₂ hB
            change _ ≤ H at hg
            dsimp only
            split
            · dsimp only; omega
            · split <;> dsimp only <;> omega
    · dsimp only; omega
  have hfinal : 16 * H ≤ u ^ 10 * (C + 1) := by
    have h : 16 * u ^ 9 ≤ u ^ 10 := by
      calc
        _ ≤ u * u ^ 9 := Nat.mul_le_mul_right _ (by omega)
        _ = _ := (pow_succ' _ _).symm
    simpa only [H, Nat.mul_assoc] using Nat.mul_le_mul_right (C + 1) h
  exact hpeak.trans hfinal

end LowSpaceSubsetSum.RepresentationStepCells

end OAI
