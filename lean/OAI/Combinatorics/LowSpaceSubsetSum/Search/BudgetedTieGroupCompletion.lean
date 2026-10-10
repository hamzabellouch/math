import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedTieGroup
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedTieRemaining

namespace OAI

namespace LowSpaceSubsetSum.BudgetedTieGroup

universe u v s t w
variable {α : Type u} {β : Type v} {σ₁ : Type s} {σ₂ : Type t} {τ : Type w}

/-- Proof-only allowance for the operations performed by this tie group. -/
def allowance (frontCharge fillCharge outerCharge charge copyCharge : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ)
    (cells : β → ℕ) (K : ℤ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ₂ → σ₂ × ℕ) (B fuel₁ fuel₂ : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ) : ℕ :=
  let f := (CountedFill.fill read₂ key₂ cells K B s₂).1
  let long := (CountedFill.hasKey read₂ key₂ K f.cursor).1
  let present := (CountedFill.hasKey read₁ key₁ K s₁).1
  let need := long && present
  let saved := if need then (clone f.cursor).1 else f.cursor
  frontCharge + fillCharge * (f.queries + 1) + (if need then copyCharge else 0) +
    BudgetedTieOuter.allowance outerCharge charge copyCharge read₁ key₁ read₂ key₂ K report clone
      f.buffer saved long fuel₁ fuel₂ s₁ ⟨f.cursor, a, 0, 0, 0⟩

theorem execute_complete (frontCharge fillCharge outerCharge charge copyCharge : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ)
    (cells : β → ℕ) (K : ℤ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ₂ → σ₂ × ℕ) (B fuel₁ fuel₂ : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ) (budget : ℕ)
    (hb : allowance frontCharge fillCharge outerCharge charge copyCharge read₁ key₁ read₂ key₂ cells K
      report clone B fuel₁ fuel₂ s₁ s₂ a ≤ budget) :
    ∃ left, (execute frontCharge fillCharge outerCharge charge copyCharge read₁ key₁ read₂ key₂ cells K
      report clone B fuel₁ fuel₂ s₁ s₂ a budget).1 =
      some ((CountedTieGroup.run read₁ key₁ read₂ key₂ cells K report clone B fuel₁ fuel₂ s₁ s₂ a).1, left) := by
  let f := (CountedFill.fill read₂ key₂ cells K B s₂).1
  let long := (CountedFill.hasKey read₂ key₂ K f.cursor).1
  let present := (CountedFill.hasKey read₁ key₁ K s₁).1
  let need := long && present
  let saved := if need then (clone f.cursor).1 else f.cursor
  let outerAllowance := BudgetedTieOuter.allowance outerCharge charge copyCharge read₁ key₁ read₂ key₂ K
    report clone f.buffer saved long fuel₁ fuel₂ s₁ ⟨f.cursor, a, 0, 0, 0⟩
  change frontCharge + fillCharge * (f.queries + 1) + (if need then copyCharge else 0) + outerAllowance ≤ budget at hb
  have hfront : frontCharge ≤ budget := by omega
  have hfill : fillCharge * (f.queries + 1) ≤ budget - frontCharge := by omega
  obtain ⟨left, hf⟩ := BudgetedFill.execute_complete fillCharge read₂ key₂ cells K B s₂ #[] 0
    (budget - frontCharge) (by
      change fillCharge * (f.queries - 0 + 1) ≤ budget - frontCharge
      simpa only [Nat.sub_zero] using hfill)
  change (BudgetedFill.execute fillCharge read₂ key₂ cells K B s₂ #[] 0 (budget - frontCharge)).1 =
    some (f, left) at hf
  have hremaining := BudgetedFill.execute_remaining fillCharge read₂ key₂ cells K B s₂ #[] 0
    (budget - frontCharge) f left hf
  simp only [Nat.sub_zero] at hremaining
  have hcopy : (if need then copyCharge else 0) ≤ left := by omega
  obtain ⟨available, hsn, havailable⟩ := BudgetedSnapshot.complete copyCharge clone need f.cursor left hcopy
  change (BudgetedSnapshot.execute copyCharge clone need f.cursor left).1 = some (saved, available) at hsn
  have hout : outerAllowance ≤ available := by omega
  obtain ⟨rest, ho⟩ := BudgetedTieOuter.execute_complete outerCharge charge copyCharge read₁ key₁ read₂ key₂ K
    report clone f.buffer saved long fuel₁ fuel₂ s₁ ⟨f.cursor, a, 0, 0, 0⟩ available hout
  let combined : TieGroup.Result σ₁ σ₂ τ :=
    ⟨(BudgetedTieOuter.reference read₁ key₁ read₂ key₂ K report clone f.buffer saved long
      fuel₁ fuel₂ s₁ ⟨f.cursor, a, 0, 0, 0⟩).1, f.queries, f.buffer.size, need⟩
  have he : (execute frontCharge fillCharge outerCharge charge copyCharge read₁ key₁ read₂ key₂ cells K
      report clone B fuel₁ fuel₂ s₁ s₂ a budget).1 = some (combined, rest) := by
    rw [execute, ite_eq_left hfront]
    simp only [hf]
    change (match (BudgetedSnapshot.execute copyCharge clone need f.cursor left).1 with
      | none => (none, _)
      | some (s, b) => _).1 = _
    rw [hsn]
    dsimp only
    dsimp only [long] at ho
    rw [ho]
    rfl
  have hv := (execute_value frontCharge fillCharge outerCharge charge copyCharge read₁ key₁ read₂ key₂ cells K
    report clone B fuel₁ fuel₂ s₁ s₂ a budget combined rest he).1
  exact ⟨rest, he.trans (congrArg (fun x => some (x, rest)) hv)⟩

theorem execute_spent
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
    (B fuel₁ fuel₂ : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ) (budget : ℕ)
    (out : TieGroup.Result σ₁ σ₂ τ) (remaining : ℕ)
    (h : (execute frontCharge fillCharge outerCharge charge copyCharge read₁ key₁ read₂ key₂ cells K
      report clone B fuel₁ fuel₂ s₁ s₂ a budget).1 = some (out, remaining)) :
    (execute frontCharge fillCharge outerCharge charge copyCharge read₁ key₁ read₂ key₂ cells K
      report clone B fuel₁ fuel₂ s₁ s₂ a budget).2 ≤ budget - remaining := by
  let filled := BudgetedFill.execute fillCharge read₂ key₂ cells K B s₂ #[] 0 (budget - frontCharge)
  have hfilled : BudgetedFill.execute fillCharge read₂ key₂ cells K B s₂ #[] 0
      (budget - frontCharge) = filled := rfl
  rw [execute] at h ⊢
  split at h
  next hb =>
    simp only [hb, ↓reduceIte, hfilled] at h ⊢
    cases hf : filled.1 with
    | none => simp only [hf] at h; contradiction
    | some p =>
      rcases p with ⟨f, left⟩
      have hfv := BudgetedFill.execute_value fillCharge read₂ key₂ cells K B s₂ #[] 0
        (budget - frontCharge) f left hf
      have hfs := BudgetedFill.execute_spent read₂ key₂ cells K R₂ L₂ S fillCharge hr₂ hk₂ hs hfill
        B s₂ #[] 0 (budget - frontCharge) f left hf
      change filled.2 ≤ budget - frontCharge - left at hfs
      have hlong := CountedFill.hasKey_work read₂ key₂ K R₂ L₂ hr₂ hk₂ f.cursor
      have hpresent := CountedFill.hasKey_work read₁ key₁ K R₁ L₁ hr₁ hk₁ s₁
      simp only [hf] at h ⊢
      let need := (CountedFill.hasKey read₂ key₂ K f.cursor).1 && (CountedFill.hasKey read₁ key₁ K s₁).1
      let snap := BudgetedSnapshot.execute copyCharge clone need f.cursor left
      change (match snap.1 with
        | none => (none, _)
        | some (saved, available) => _).1 = some (out, remaining) at h
      cases hsn : snap.1 with
      | none => simp only [hsn] at h; contradiction
      | some p =>
        rcases p with ⟨saved, available⟩
        have hsv := BudgetedSnapshot.value copyCharge clone need f.cursor left saved available hsn
        have hss := BudgetedSnapshot.spent copyCharge clone hcopy need f.cursor left saved available hsn
        change snap.2 ≤ left - available at hss
        simp only [hsn] at h
        obtain ⟨pair, ho, he⟩ := Option.map_eq_some_iff.mp h
        rcases pair with ⟨outer, rest⟩
        have hos := BudgetedTieOuter.execute_spent read₁ key₁ read₂ key₂ K report clone
          R₁ L₁ R₂ L₂ C outerCharge charge copyCharge hr₁ hk₁ hr₂ hk₂ hc houter hcharge hcopy
          f.buffer saved (CountedFill.hasKey read₂ key₂ K f.cursor).1 fuel₁ fuel₂ s₁
          ⟨f.cursor, a, 0, 0, 0⟩ available outer rest ho
        cases he
        change filled.2 + (CountedFill.hasKey read₂ key₂ K f.cursor).2 +
          (CountedFill.hasKey read₁ key₁ K s₁).2 + snap.2 +
          (BudgetedTieOuter.execute outerCharge charge copyCharge read₁ key₁ read₂ key₂ K
            report clone f.buffer saved (CountedFill.hasKey read₂ key₂ K f.cursor).1
            fuel₁ fuel₂ s₁ ⟨f.cursor, a, 0, 0, 0⟩ available).2 + 8 ≤ budget - rest
        omega
  next _ => contradiction

theorem execute_remaining (frontCharge fillCharge outerCharge charge copyCharge : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ)
    (cells : β → ℕ) (K : ℤ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ₂ → σ₂ × ℕ) (B fuel₁ fuel₂ : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ) (budget : ℕ)
    (out : TieGroup.Result σ₁ σ₂ τ) (remaining : ℕ)
    (h : (execute frontCharge fillCharge outerCharge charge copyCharge read₁ key₁ read₂ key₂ cells K
      report clone B fuel₁ fuel₂ s₁ s₂ a budget).1 = some (out, remaining)) :
    budget ≤ remaining + allowance frontCharge fillCharge outerCharge charge copyCharge
      read₁ key₁ read₂ key₂ cells K report clone B fuel₁ fuel₂ s₁ s₂ a := by
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
      have hfr := BudgetedFill.execute_remaining fillCharge read₂ key₂ cells K B s₂ #[] 0
        (budget - frontCharge) f left hf
      simp only [Nat.sub_zero] at hfr
      simp only [hf] at h
      let need := (CountedFill.hasKey read₂ key₂ K f.cursor).1 && (CountedFill.hasKey read₁ key₁ K s₁).1
      let snap := BudgetedSnapshot.execute copyCharge clone need f.cursor left
      change (match snap.1 with
        | none => (none, _)
        | some (saved, available) => _).1 = some (out, remaining) at h
      cases hsn : snap.1 with
      | none => simp only [hsn] at h; contradiction
      | some p =>
        rcases p with ⟨saved, available⟩
        have hsv := BudgetedSnapshot.value copyCharge clone need f.cursor left saved available hsn
        have hsr := BudgetedSnapshot.remaining copyCharge clone need f.cursor left saved available hsn
        simp only [hsn] at h
        obtain ⟨pair, ho, he⟩ := Option.map_eq_some_iff.mp h
        rcases pair with ⟨outer, rest⟩
        have hor := BudgetedTieOuter.execute_remaining outerCharge charge copyCharge
          read₁ key₁ read₂ key₂ K report clone f.buffer saved
          (CountedFill.hasKey read₂ key₂ K f.cursor).1 fuel₁ fuel₂ s₁
          ⟨f.cursor, a, 0, 0, 0⟩ available outer rest ho
        cases he
        have hfref : (CountedFill.fill read₂ key₂ cells K B s₂).1 = f := hfv.1.symm
        unfold allowance
        rw [hfref]
        change budget ≤ rest + (frontCharge + fillCharge * (f.queries + 1) +
          (if need then copyCharge else 0) + BudgetedTieOuter.allowance outerCharge charge copyCharge
            read₁ key₁ read₂ key₂ K report clone f.buffer
            (if need then (clone f.cursor).1 else f.cursor)
            (CountedFill.hasKey read₂ key₂ K f.cursor).1 fuel₁ fuel₂ s₁ ⟨f.cursor, a, 0, 0, 0⟩)
        rw [← hsv.1]
        omega
  next _ => contradiction

/-- The prepaid allowance is linear in the exact group's query/copy ledger. -/
theorem allowance_le (frontCharge fillCharge outerCharge charge copyCharge : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ)
    (cells : β → ℕ) (K : ℤ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ₂ → σ₂ × ℕ) (B fuel₁ fuel₂ : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ) :
    let out := (CountedTieGroup.run read₁ key₁ read₂ key₂ cells K report clone B fuel₁ fuel₂ s₁ s₂ a).1
    allowance frontCharge fillCharge outerCharge charge copyCharge read₁ key₁ read₂ key₂ cells K
      report clone B fuel₁ fuel₂ s₁ s₂ a ≤
      (frontCharge + fillCharge + outerCharge + 2 * charge + 12) *
        (out.outer.queries + out.fillQueries + out.outer.state.queries + 1) +
      copyCharge * ((if out.snapshot then 1 else 0) + out.outer.state.restores) := by
  let f := (CountedFill.fill read₂ key₂ cells K B s₂).1
  let long := (CountedFill.hasKey read₂ key₂ K f.cursor).1
  let present := (CountedFill.hasKey read₁ key₁ K s₁).1
  let need := long && present
  let saved := if need then (clone f.cursor).1 else f.cursor
  let out := (BudgetedTieOuter.reference read₁ key₁ read₂ key₂ K report clone f.buffer saved long
    fuel₁ fuel₂ s₁ ⟨f.cursor, a, 0, 0, 0⟩).1
  have hsaved : saved = (if need then clone f.cursor else (f.cursor, 0)).1 := by
    dsimp only [saved]
    cases need <;> rfl
  have hout : (CountedTieGroup.run read₁ key₁ read₂ key₂ cells K report clone B fuel₁ fuel₂ s₁ s₂ a).1 =
      ⟨out, f.queries, f.buffer.size, need⟩ := by
    dsimp only [CountedTieGroup.run]
    change _ = (⟨(CountedReplay.run read₁ key₁ K
      (CountedTieGroup.step read₂ key₂ K report clone f.buffer saved long fuel₂)
      fuel₁ s₁ ⟨f.cursor, a, 0, 0, 0⟩).1, f.queries, f.buffer.size, need⟩ : TieGroup.Result σ₁ σ₂ τ)
    rw [hsaved]
  rw [hout]
  have ho := BudgetedTieOuter.allowance_le outerCharge charge copyCharge read₁ key₁ read₂ key₂ K
    report clone f.buffer saved long fuel₁ fuel₂ s₁ ⟨f.cursor, a, 0, 0, 0⟩
  change BudgetedTieOuter.allowance outerCharge charge copyCharge read₁ key₁ read₂ key₂ K
    report clone f.buffer saved long fuel₁ fuel₂ s₁ ⟨f.cursor, a, 0, 0, 0⟩ ≤
    (outerCharge + 2 * charge + 12) * out.queries +
      (charge * out.state.queries + copyCharge * out.state.restores) + outerCharge at ho
  let M := frontCharge + fillCharge + outerCharge + 2 * charge + 12
  have hq := Nat.mul_le_mul_right out.queries (show outerCharge + 2 * charge + 12 ≤ M by dsimp [M]; omega)
  have hf := Nat.mul_le_mul_right f.queries (show fillCharge ≤ M by dsimp [M]; omega)
  have hi := Nat.mul_le_mul_right out.state.queries (show charge ≤ M by dsimp [M]; omega)
  have hbase : frontCharge + fillCharge + outerCharge ≤ M := by dsimp [M]; omega
  have hcp : (if need then copyCharge else 0) = copyCharge * (if need then 1 else 0) := by
    cases need <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.mul_one]
  change frontCharge + fillCharge * (f.queries + 1) + (if need then copyCharge else 0) +
    BudgetedTieOuter.allowance outerCharge charge copyCharge read₁ key₁ read₂ key₂ K report clone
      f.buffer saved long fuel₁ fuel₂ s₁ ⟨f.cursor, a, 0, 0, 0⟩ ≤
    M * (out.queries + f.queries + out.state.queries + 1) +
      copyCharge * ((if need then 1 else 0) + out.state.restores)
  rw [hcp]
  simp only [Nat.mul_add, Nat.mul_one]
  omega

end LowSpaceSubsetSum.BudgetedTieGroup

end OAI
