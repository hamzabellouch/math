import OAI.Combinatorics.LowSpaceSubsetSum.Storage.ScalarGroupCells
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedStreamStep

namespace OAI

/-! # Scalar sorted-join steps with both fetched cursors retained -/

namespace LowSpaceSubsetSum.ScalarStepCells

universe u v w
variable {σ₁ : Type u} {σ₂ : Type v} {τ : Type w}

def frame (cells₁ : σ₁ → ℕ) (cells₂ : σ₂ → ℕ) (userCells : τ → ℕ)
    (st : StreamJoin.State σ₁ σ₂ τ) : ℕ :=
  cells₁ st.left+cells₂ st.right+userCells st.user+32

def run (base front fill outer inner copy : ℕ)
    (read₁ : σ₁ → (Option (ℤ × σ₁) × ℕ) × ℕ) (key₁ : ℤ → (ℤ × ℕ) × ℕ)
    (read₂ : σ₂ → (Option (ℤ × σ₂) × ℕ) × ℕ) (key₂ : ℤ → (ℤ × ℕ) × ℕ)
    (report : ℤ → ℤ → τ → ((τ × Bool) × ℕ) × ℕ) (clone : σ₂ → (σ₂ × ℕ) × ℕ)
    (cells₁ : σ₁ → ℕ) (cells₂ : σ₂ → ℕ) (userCells : τ → ℕ)
    (B fuel₁ fuel₂ : ℕ) (st : StreamJoin.State σ₁ σ₂ τ) (budget : ℕ) :
    (Option (StreamJoin.State σ₁ σ₂ τ × ℕ) × ℕ) × ℕ :=
  let retained := frame cells₁ cells₂ userCells st
  if base ≤ budget then
    if st.done then ((some (st,budget-base),1),retained) else
    let x := read₁ st.left
    let firstPeak := retained+x.2+16
    match x.1.1 with
    | none => ((some ({st with queries := st.queries+1, done := true},budget-base),x.1.2+4),firstPeak)
    | some (a,left) =>
      let y := read₂ st.right
      let secondPeak := max firstPeak (retained+cells₁ left+y.2+17)
      match y.1.1 with
      | none => ((some ({st with queries := st.queries+2,done := true},budget-base),x.1.2+y.1.2+5),secondPeak)
      | some (b,right) =>
        let k₁ := key₁ a
        let k₂ := key₂ b
        let live := retained+cells₁ left+cells₂ right+66
        let peak := max secondPeak (live+k₁.2+k₂.2)
        if k₁.1.1 < k₂.1.1 then
          ((some ({st with left := left,queries := st.queries+2},budget-base),
            x.1.2+y.1.2+k₁.1.2+k₂.1.2+8),peak)
        else if k₂.1.1 < k₁.1.1 then
          ((some ({st with right := right,queries := st.queries+2},budget-base),
            x.1.2+y.1.2+k₁.1.2+k₂.1.2+8),peak)
        else
          let out := ScalarGroupCells.run front fill outer inner copy read₁ key₁ read₂ key₂
            report clone cells₁ cells₂ userCells k₁.1.1 B fuel₁ fuel₂ st.left st.right st.user (budget-base)
          ((out.1.1.map (fun (group,left) => (BudgetedStreamStep.advance st group,left)),
            x.1.2+y.1.2+k₁.1.2+k₂.1.2+out.1.2+16),max peak (live+out.2))
  else ((none,1),retained)

theorem run_value (base front fill outer inner copy : ℕ)
    (read₁ : σ₁ → (Option (ℤ × σ₁) × ℕ) × ℕ) (key₁ : ℤ → (ℤ × ℕ) × ℕ)
    (read₂ : σ₂ → (Option (ℤ × σ₂) × ℕ) × ℕ) (key₂ : ℤ → (ℤ × ℕ) × ℕ)
    (report : ℤ → ℤ → τ → ((τ × Bool) × ℕ) × ℕ) (clone : σ₂ → (σ₂ × ℕ) × ℕ)
    (cells₁ : σ₁ → ℕ) (cells₂ : σ₂ → ℕ) (userCells : τ → ℕ)
    (B fuel₁ fuel₂ : ℕ) (st : StreamJoin.State σ₁ σ₂ τ) (budget : ℕ) :
    (run base front fill outer inner copy read₁ key₁ read₂ key₂ report clone
      cells₁ cells₂ userCells B fuel₁ fuel₂ st budget).1 =
      BudgetedStreamStep.execute base front fill outer inner copy
        (fun s => (read₁ s).1) (fun x => (key₁ x).1) (fun s => (read₂ s).1) (fun y => (key₂ y).1)
        (fun _ => 1) (fun x y a => (report x y a).1) (fun s => (clone s).1)
        B fuel₁ fuel₂ st budget := by
  unfold run BudgetedStreamStep.execute
  dsimp only
  split
  · split
    · rfl
    · cases hx : (read₁ st.left).1.1 with
      | none => rfl
      | some p =>
        rcases p with ⟨a,left⟩
        dsimp only
        cases hy : (read₂ st.right).1.1 with
        | none => rfl
        | some p =>
          rcases p with ⟨b,right⟩
          dsimp only
          simp only [ScalarGroupCells.run_value]
          split
          · rfl
          · split <;> rfl
  · rfl

theorem frame_cells (cells₁ : σ₁ → ℕ) (cells₂ : σ₂ → ℕ) (userCells : τ → ℕ)
    (H : ℕ) (hH : 100 ≤ H) (hs₁ : ∀ s, cells₁ s ≤ H) (hs₂ : ∀ s, cells₂ s ≤ H)
    (hu : ∀ a, userCells a ≤ H) (st : StreamJoin.State σ₁ σ₂ τ) :
    frame cells₁ cells₂ userCells st ≤ 4*H := by
  have h₁ := hs₁ st.left
  have h₂ := hs₂ st.right
  have h₃ := hu st.user
  unfold frame
  omega

theorem run_cells (base front fill outer inner copy : ℕ)
    (read₁ : σ₁ → (Option (ℤ × σ₁) × ℕ) × ℕ) (key₁ : ℤ → (ℤ × ℕ) × ℕ)
    (read₂ : σ₂ → (Option (ℤ × σ₂) × ℕ) × ℕ) (key₂ : ℤ → (ℤ × ℕ) × ℕ)
    (report : ℤ → ℤ → τ → ((τ × Bool) × ℕ) × ℕ) (clone : σ₂ → (σ₂ × ℕ) × ℕ)
    (cells₁ : σ₁ → ℕ) (cells₂ : σ₂ → ℕ) (userCells : τ → ℕ)
    (H : ℕ) (hH : 100 ≤ H) (hs₁ : ∀ s, cells₁ s ≤ H) (hs₂ : ∀ s, cells₂ s ≤ H)
    (hu : ∀ a, userCells a ≤ H)
    (hr₁ : ∀ s, (read₁ s).2 ≤ H) (hr₂ : ∀ s, (read₂ s).2 ≤ H)
    (hk₁ : ∀ x, (key₁ x).2 ≤ H) (hk₂ : ∀ x, (key₂ x).2 ≤ H)
    (hp : ∀ x y a, (report x y a).2 ≤ H) (hc : ∀ s, (clone s).2 ≤ H)
    (B fuel₁ fuel₂ : ℕ) (hB : B ≤ H) (st : StreamJoin.State σ₁ σ₂ τ) (budget : ℕ) :
    (run base front fill outer inner copy read₁ key₁ read₂ key₂ report clone
      cells₁ cells₂ userCells B fuel₁ fuel₂ st budget).2 ≤ 56*H := by
  have hret := frame_cells cells₁ cells₂ userCells H hH hs₁ hs₂ hu st
  have hxw := hr₁ st.left
  have hyw := hr₂ st.right
  unfold run
  dsimp only
  split
  · split
    · dsimp only; omega
    · cases hx : (read₁ st.left).1.1 with
      | none => dsimp only; omega
      | some p =>
        rcases p with ⟨a,left⟩
        have hleft := hs₁ left
        dsimp only
        cases hy : (read₂ st.right).1.1 with
        | none => dsimp only; omega
        | some p =>
          rcases p with ⟨b,right⟩
          have hright := hs₂ right
          have hk₁' := hk₁ a
          have hk₂' := hk₂ b
          have hg := ScalarGroupCells.run_cells front fill outer inner copy read₁ key₁ read₂ key₂
            report clone cells₁ cells₂ userCells H hH hs₁ hs₂ hu hr₁ hr₂ hk₁ hk₂ hp hc
            (key₁ a).1.1 B fuel₁ fuel₂ hB st.left st.right st.user (budget-base)
          dsimp only
          split
          · dsimp only; omega
          · split <;> dsimp only <;> omega
  · dsimp only; omega

end LowSpaceSubsetSum.ScalarStepCells

end OAI
