import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedTieOuter
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedSnapshot

namespace OAI

/-! # A single prepaid allowance for an entire Cartesian tie group -/

namespace LowSpaceSubsetSum.BudgetedTieGroup

universe u v s t w
variable {α : Type u} {β : Type v} {σ₁ : Type s} {σ₂ : Type t} {τ : Type w}

def execute (frontCharge fillCharge outerCharge charge copyCharge : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ)
    (cells : β → ℕ) (K : ℤ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ₂ → σ₂ × ℕ) (B fuel₁ fuel₂ : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ) (budget : ℕ) :
    Option (TieGroup.Result σ₁ σ₂ τ × ℕ) × ℕ :=
  if frontCharge ≤ budget then
    let filled := BudgetedFill.execute fillCharge read₂ key₂ cells K B s₂ #[] 0 (budget - frontCharge)
    match filled.1 with
    | none => (none, filled.2 + 1)
    | some (f, left) =>
      let long := CountedFill.hasKey read₂ key₂ K f.cursor
      let present := CountedFill.hasKey read₁ key₁ K s₁
      let snap := BudgetedSnapshot.execute copyCharge clone (long.1 && present.1) f.cursor left
      match snap.1 with
      | none => (none, filled.2 + long.2 + present.2 + snap.2 + 8)
      | some (saved, remaining) =>
        let out := BudgetedTieOuter.execute outerCharge charge copyCharge read₁ key₁ read₂ key₂ K
          report clone f.buffer saved long.1 fuel₁ fuel₂ s₁ ⟨f.cursor, a, 0, 0, 0⟩ remaining
        (out.1.map (fun (outer, rest) =>
          (⟨outer, f.queries, f.buffer.size, long.1 && present.1⟩, rest)),
          filled.2 + long.2 + present.2 + snap.2 + out.2 + 8)
  else (none, 1)

theorem execute_work
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ)
    (cells : β → ℕ) (K : ℤ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ₂ → σ₂ × ℕ)
    (R₁ L₁ R₂ L₂ S C frontCharge fillCharge outerCharge charge copyCharge : ℕ)
    (hr₁ : ∀ s, (read₁ s).2 ≤ R₁) (hk₁ : ∀ x, (key₁ x).2 ≤ L₁)
    (hr₂ : ∀ s, (read₂ s).2 ≤ R₂) (hk₂ : ∀ y, (key₂ y).2 ≤ L₂)
    (hs : ∀ y, cells y ≤ S) (hc : ∀ x y a, (report x y a).2 ≤ C)
    (hfront : R₁ + L₁ + R₂ + L₂ + 16 ≤ frontCharge)
    (hfill : R₂ + L₂ + S + 8 ≤ fillCharge) (houter : R₁ + L₁ + 8 ≤ outerCharge)
    (hcharge : max R₂ 4 + L₂ + C + 8 ≤ charge) (hcopy : ∀ s, (clone s).2 ≤ copyCharge)
    (B fuel₁ fuel₂ : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ) (budget : ℕ) :
    (execute frontCharge fillCharge outerCharge charge copyCharge read₁ key₁ read₂ key₂ cells K report
      clone B fuel₁ fuel₂ s₁ s₂ a budget).2 ≤ budget + 1 := by
  let filled := BudgetedFill.execute fillCharge read₂ key₂ cells K B s₂ #[] 0 (budget - frontCharge)
  have hfilled : BudgetedFill.execute fillCharge read₂ key₂ cells K B s₂ #[] 0
      (budget - frontCharge) = filled := rfl
  have hfw := BudgetedFill.execute_work read₂ key₂ cells K R₂ L₂ S fillCharge hr₂ hk₂ hs hfill
    B s₂ #[] 0 (budget - frontCharge)
  change filled.2 ≤ budget - frontCharge + 1 at hfw
  rw [execute]
  split
  next hb =>
    simp only [hfilled]
    cases hf : filled.1 with
    | none => (try dsimp only); omega
    | some p =>
      rcases p with ⟨f, left⟩
      have hfv := BudgetedFill.execute_value fillCharge read₂ key₂ cells K B s₂ #[] 0
        (budget - frontCharge) f left hf
      have hfs := BudgetedFill.execute_spent read₂ key₂ cells K R₂ L₂ S fillCharge hr₂ hk₂ hs hfill
        B s₂ #[] 0 (budget - frontCharge) f left hf
      change filled.2 ≤ budget - frontCharge - left at hfs
      have hlong := CountedFill.hasKey_work read₂ key₂ K R₂ L₂ hr₂ hk₂ f.cursor
      have hpresent := CountedFill.hasKey_work read₁ key₁ K R₁ L₁ hr₁ hk₁ s₁
      let need := (CountedFill.hasKey read₂ key₂ K f.cursor).1 && (CountedFill.hasKey read₁ key₁ K s₁).1
      let snap := BudgetedSnapshot.execute copyCharge clone need f.cursor left
      have hsnap : BudgetedSnapshot.execute copyCharge clone need f.cursor left = snap := rfl
      have hsw := BudgetedSnapshot.work copyCharge clone hcopy need f.cursor left
      change snap.2 ≤ left + 1 at hsw
      dsimp only
      change (match snap.1 with
        | none => (none, filled.2 + _ + _ + snap.2 + 8)
        | some (saved, remaining) => _).2 ≤ _
      cases hsn : snap.1 with
      | none => (try dsimp only); omega
      | some p =>
        rcases p with ⟨saved, remaining⟩
        have hss := BudgetedSnapshot.spent copyCharge clone hcopy need f.cursor left saved remaining hsn
        have hsv := BudgetedSnapshot.value copyCharge clone need f.cursor left saved remaining hsn
        change snap.2 ≤ left - remaining at hss
        have how := BudgetedTieOuter.execute_work read₁ key₁ read₂ key₂ K report clone
          R₁ L₁ R₂ L₂ C outerCharge charge copyCharge hr₁ hk₁ hr₂ hk₂ hc houter hcharge hcopy
          f.buffer saved (CountedFill.hasKey read₂ key₂ K f.cursor).1 fuel₁ fuel₂ s₁
          ⟨f.cursor, a, 0, 0, 0⟩ remaining
        change filled.2 + (CountedFill.hasKey read₂ key₂ K f.cursor).2 +
          (CountedFill.hasKey read₁ key₁ K s₁).2 + snap.2 +
          (BudgetedTieOuter.execute outerCharge charge copyCharge read₁ key₁ read₂ key₂ K
            report clone f.buffer saved (CountedFill.hasKey read₂ key₂ K f.cursor).1
            fuel₁ fuel₂ s₁ ⟨f.cursor, a, 0, 0, 0⟩ remaining).2 + 8 ≤ budget + 1
        omega
  next _ => (try dsimp only); omega

theorem execute_value (frontCharge fillCharge outerCharge charge copyCharge : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ)
    (cells : β → ℕ) (K : ℤ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ₂ → σ₂ × ℕ) (B fuel₁ fuel₂ : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ) (budget : ℕ)
    (out : TieGroup.Result σ₁ σ₂ τ) (remaining : ℕ)
    (h : (execute frontCharge fillCharge outerCharge charge copyCharge read₁ key₁ read₂ key₂ cells K report
      clone B fuel₁ fuel₂ s₁ s₂ a budget).1 = some (out, remaining)) :
    out = (CountedTieGroup.run read₁ key₁ read₂ key₂ cells K report clone B fuel₁ fuel₂ s₁ s₂ a).1 ∧
      remaining ≤ budget := by
  let filled := BudgetedFill.execute fillCharge read₂ key₂ cells K B s₂ #[] 0 (budget - frontCharge)
  have hfilled : BudgetedFill.execute fillCharge read₂ key₂ cells K B s₂ #[] 0
      (budget - frontCharge) = filled := rfl
  rw [execute] at h
  split at h
  next hb =>
    simp only [hfilled] at h
    cases hf : filled.1 with
    | none => simp only [hf] at h; contradiction
    | some p =>
      rcases p with ⟨f, left⟩
      have hfv := BudgetedFill.execute_value fillCharge read₂ key₂ cells K B s₂ #[] 0
        (budget - frontCharge) f left hf
      simp only [hf] at h
      let need := (CountedFill.hasKey read₂ key₂ K f.cursor).1 && (CountedFill.hasKey read₁ key₁ K s₁).1
      let snap := BudgetedSnapshot.execute copyCharge clone need f.cursor left
      have hsnap : BudgetedSnapshot.execute copyCharge clone need f.cursor left = snap := rfl
      change (match snap.1 with
        | none => (none, _)
        | some (saved, available) => _).1 = some (out, remaining) at h
      cases hsn : snap.1 with
      | none => simp only [hsn] at h; contradiction
      | some p =>
        rcases p with ⟨saved, available⟩
        have hsv := BudgetedSnapshot.value copyCharge clone need f.cursor left saved available hsn
        simp only [hsn] at h
        obtain ⟨pair, ho, he⟩ := Option.map_eq_some_iff.mp h
        rcases pair with ⟨outer, final⟩
        have hov := BudgetedTieOuter.execute_value outerCharge charge copyCharge
          read₁ key₁ read₂ key₂ K report clone f.buffer saved
          (CountedFill.hasKey read₂ key₂ K f.cursor).1 fuel₁ fuel₂ s₁
          ⟨f.cursor, a, 0, 0, 0⟩ available outer final ho
        cases he
        refine ⟨?_, hov.2.trans (hsv.2.trans (hfv.2.trans (Nat.sub_le _ _)))⟩
        rw [hov.1, hsv.1]
        rcases hfv with ⟨rfl, hleft⟩
        unfold BudgetedTieOuter.reference CountedTieGroup.run
        dsimp only [CountedFill.fill]
        have hcast (b : Bool) (s : σ₂) :
            (if b then (clone s).1 else s) = (if b then clone s else (s, 0)).1 := by
          cases b <;> rfl
        rw [hcast]
  next _ => contradiction

end LowSpaceSubsetSum.BudgetedTieGroup

end OAI
