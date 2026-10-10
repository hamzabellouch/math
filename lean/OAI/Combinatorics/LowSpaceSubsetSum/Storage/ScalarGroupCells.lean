import OAI.Combinatorics.LowSpaceSubsetSum.Storage.ScalarTieOuterCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.ScalarObservationCells
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedTieGroup

namespace OAI

/-! # Complete scalar tie groups, including every stopped branch -/

namespace LowSpaceSubsetSum.ScalarGroupCells

universe u v w
variable {σ₁ : Type u} {σ₂ : Type v} {τ : Type w}

def run (front fill outer inner copy : ℕ)
    (read₁ : σ₁ → (Option (ℤ × σ₁) × ℕ) × ℕ) (key₁ : ℤ → (ℤ × ℕ) × ℕ)
    (read₂ : σ₂ → (Option (ℤ × σ₂) × ℕ) × ℕ) (key₂ : ℤ → (ℤ × ℕ) × ℕ)
    (report : ℤ → ℤ → τ → ((τ × Bool) × ℕ) × ℕ) (clone : σ₂ → (σ₂ × ℕ) × ℕ)
    (cells₁ : σ₁ → ℕ) (cells₂ : σ₂ → ℕ) (userCells : τ → ℕ) (K : ℤ)
    (B fuel₁ fuel₂ : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ) (budget : ℕ) :
    (Option (TieGroup.Result σ₁ σ₂ τ × ℕ) × ℕ) × ℕ :=
  let retained := cells₁ s₁+cells₂ s₂+userCells a+32
  if front ≤ budget then
    let filled := BudgetedFillCells.run fill read₂ key₂ (fun _ => 1) cells₂ K B s₂ (budget-front)
    let peak := retained+filled.2+16
    match filled.1.1 with
    | none => ((none,filled.1.2+1),peak)
    | some (f,left) =>
      let bufferCells := 2*f.buffer.size+1
      let long := ScalarObservationCells.hasKey read₂ key₂ cells₂ K f.cursor
      let present := ScalarObservationCells.hasKey read₁ key₁ cells₁ K s₁
      let snap := ScalarObservationCells.snapshot clone copy (long.1.1 && present.1.1) f.cursor left
      let peak := max peak (retained+bufferCells+cells₂ f.cursor+long.2+present.2+snap.2+32)
      match snap.1.1 with
      | none => ((none,filled.1.2+long.1.2+present.1.2+snap.1.2+8),peak)
      | some (saved,remaining) =>
        let out := ScalarTieOuterCells.run outer inner copy read₁ key₁ read₂ key₂ K report clone
          cells₁ cells₂ userCells f.buffer saved long.1.1 fuel₁ fuel₂ s₁ ⟨f.cursor,a,0,0,0⟩ remaining
        ((out.1.1.map (fun (out,rest) => (⟨out,f.queries,f.buffer.size,long.1.1 && present.1.1⟩,rest)),
          filled.1.2+long.1.2+present.1.2+snap.1.2+out.1.2+8),
          max peak (retained+bufferCells+cells₂ f.cursor+out.2+32))
  else ((none,1),retained)

theorem run_value (front fill outer inner copy : ℕ)
    (read₁ : σ₁ → (Option (ℤ × σ₁) × ℕ) × ℕ) (key₁ : ℤ → (ℤ × ℕ) × ℕ)
    (read₂ : σ₂ → (Option (ℤ × σ₂) × ℕ) × ℕ) (key₂ : ℤ → (ℤ × ℕ) × ℕ)
    (report : ℤ → ℤ → τ → ((τ × Bool) × ℕ) × ℕ) (clone : σ₂ → (σ₂ × ℕ) × ℕ)
    (cells₁ : σ₁ → ℕ) (cells₂ : σ₂ → ℕ) (userCells : τ → ℕ) (K : ℤ)
    (B fuel₁ fuel₂ : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ) (budget : ℕ) :
    (run front fill outer inner copy read₁ key₁ read₂ key₂ report clone cells₁ cells₂ userCells
      K B fuel₁ fuel₂ s₁ s₂ a budget).1 =
      BudgetedTieGroup.execute front fill outer inner copy (fun s => (read₁ s).1) (fun x => (key₁ x).1)
        (fun s => (read₂ s).1) (fun y => (key₂ y).1) (fun _ => 1) K
        (fun x y a => (report x y a).1) (fun s => (clone s).1) B fuel₁ fuel₂ s₁ s₂ a budget := by
  unfold run BudgetedTieGroup.execute
  dsimp only
  split
  · simp only [BudgetedFillCells.run_value]
    cases hf : (BudgetedFill.execute fill (fun s => (read₂ s).1) (fun y => (key₂ y).1)
        (fun _ => 1) K B s₂ #[] 0 (budget-front)).1 with
    | none => rfl
    | some p =>
      rcases p with ⟨f,left⟩
      dsimp only
      simp only [ScalarObservationCells.hasKey_value,ScalarObservationCells.snapshot_value]
      cases hs : (BudgetedSnapshot.execute copy (fun s => (clone s).1)
          ((CountedFill.hasKey (fun s => (read₂ s).1) (fun y => (key₂ y).1) K f.cursor).1 &&
            (CountedFill.hasKey (fun s => (read₁ s).1) (fun x => (key₁ x).1) K s₁).1)
          f.cursor left).1 with
      | none => rfl
      | some p =>
        rcases p with ⟨saved,remaining⟩
        dsimp only
        simp only [ScalarTieOuterCells.run_value]
  · rfl

theorem run_cells (front fill outer inner copy : ℕ)
    (read₁ : σ₁ → (Option (ℤ × σ₁) × ℕ) × ℕ) (key₁ : ℤ → (ℤ × ℕ) × ℕ)
    (read₂ : σ₂ → (Option (ℤ × σ₂) × ℕ) × ℕ) (key₂ : ℤ → (ℤ × ℕ) × ℕ)
    (report : ℤ → ℤ → τ → ((τ × Bool) × ℕ) × ℕ) (clone : σ₂ → (σ₂ × ℕ) × ℕ)
    (cells₁ : σ₁ → ℕ) (cells₂ : σ₂ → ℕ) (userCells : τ → ℕ)
    (H : ℕ) (hH : 100 ≤ H) (hs₁ : ∀ s, cells₁ s ≤ H) (hs₂ : ∀ s, cells₂ s ≤ H)
    (hu : ∀ a, userCells a ≤ H)
    (hr₁ : ∀ s, (read₁ s).2 ≤ H) (hr₂ : ∀ s, (read₂ s).2 ≤ H)
    (hk₁ : ∀ x, (key₁ x).2 ≤ H) (hk₂ : ∀ x, (key₂ x).2 ≤ H)
    (hp : ∀ x y a, (report x y a).2 ≤ H) (hc : ∀ s, (clone s).2 ≤ H)
    (K : ℤ) (B fuel₁ fuel₂ : ℕ) (hB : B ≤ H) (s₁ : σ₁) (s₂ : σ₂) (a : τ) (budget : ℕ) :
    (run front fill outer inner copy read₁ key₁ read₂ key₂ report clone cells₁ cells₂ userCells
      K B fuel₁ fuel₂ s₁ s₂ a budget).2 ≤ 48*H := by
  have hret : cells₁ s₁+cells₂ s₂+userCells a+32 ≤ 4*H := by
    have h₁ := hs₁ s₁
    have h₂ := hs₂ s₂
    have h₃ := hu a
    omega
  have hf := BudgetedFillCells.run_cells fill read₂ key₂ (fun _ => 1) cells₂ K H H H 1
    hr₂ hk₂ hs₂ (fun _ => le_rfl) B s₂ (budget-front)
  have hfill : (BudgetedFillCells.run fill read₂ key₂ (fun _ => 1) cells₂ K B s₂ (budget-front)).2 ≤
      9*H := by omega
  unfold run
  dsimp only
  split
  · cases he : (BudgetedFillCells.run fill read₂ key₂ (fun _ => 1) cells₂ K B s₂ (budget-front)).1.1 with
    | none => dsimp only; omega
    | some p =>
      rcases p with ⟨f,left⟩
      have hcap : f.buffer.size ≤ H :=
        (ScalarObservationCells.fill_capacity fill read₂ key₂ cells₂ K B s₂ (budget-front) f left he).trans hB
      have hbuf : 2*f.buffer.size+1 ≤ 3*H := by omega
      have hcur := hs₂ f.cursor
      have hlong := ScalarObservationCells.hasKey_cells read₂ key₂ cells₂ H hH hs₂ hr₂ hk₂ K f.cursor
      have hpresent := ScalarObservationCells.hasKey_cells read₁ key₁ cells₁ H hH hs₁ hr₁ hk₁ K s₁
      have hsnap := ScalarObservationCells.snapshot_cells clone H hH hc copy
        ((ScalarObservationCells.hasKey read₂ key₂ cells₂ K f.cursor).1.1 &&
          (ScalarObservationCells.hasKey read₁ key₁ cells₁ K s₁).1.1) f.cursor left
      dsimp only
      cases hsn : (ScalarObservationCells.snapshot clone copy
          ((ScalarObservationCells.hasKey read₂ key₂ cells₂ K f.cursor).1.1 &&
            (ScalarObservationCells.hasKey read₁ key₁ cells₁ K s₁).1.1) f.cursor left).1.1 with
      | none => dsimp only; omega
      | some p =>
        rcases p with ⟨saved,remaining⟩
        have hout := ScalarTieOuterCells.run_cells outer inner copy read₁ key₁ read₂ key₂ K report clone
          cells₁ cells₂ userCells H hH hs₁ hs₂ hu hr₁ hr₂ hk₁ hk₂ hp hc f.buffer hcap saved
          (ScalarObservationCells.hasKey read₂ key₂ cells₂ K f.cursor).1.1 fuel₁ fuel₂ s₁
          ⟨f.cursor,a,0,0,0⟩ remaining
        dsimp only
        omega
  · dsimp only; omega

end LowSpaceSubsetSum.ScalarGroupCells

end OAI
