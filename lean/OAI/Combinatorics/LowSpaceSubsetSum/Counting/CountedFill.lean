import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedReplay

namespace OAI

/-! # Cost-carrying bounded tie-buffer construction and lookahead -/

namespace LowSpaceSubsetSum.CountedFill

universe u v
variable {α : Type u} {σ : Type v}

def fillAcc (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ)
    (cells : α → ℕ) (K : ℤ) : ℕ → σ → Array α → ℕ → TieBuffer.Result α σ × ℕ
  | 0, s, buf, q => (⟨buf, s, q⟩, 1)
  | fuel + 1, s, buf, q =>
    let fetched := read s
    match fetched.1 with
    | none => (⟨buf, s, q + 1⟩, fetched.2 + 5)
    | some (x, s') =>
      let found := key x
      if found.1 = K then
        let rest := fillAcc read key cells K fuel s' (buf.push x) (q + 1)
        (rest.1, fetched.2 + found.2 + cells x + 8 + rest.2)
      else (⟨buf, s, q + 1⟩, fetched.2 + found.2 + 6)

theorem fillAcc_value (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ)
    (cells : α → ℕ) (K : ℤ) (fuel : ℕ) (s : σ) (buf : Array α) (q : ℕ) :
    (fillAcc read key cells K fuel s buf q).1 =
      TieBuffer.fillAcc (fun s => (read s).1) (fun x => (key x).1) K fuel s buf q := by
  induction fuel generalizing s buf q with
  | zero => rfl
  | succ fuel ih =>
    cases hr : (read s).1 with
    | none => simp only [fillAcc, TieBuffer.fillAcc, hr]
    | some z =>
      rcases z with ⟨x, s'⟩
      simp only [fillAcc, TieBuffer.fillAcc, hr]
      split
      · exact ih _ _ _
      · rfl

theorem fillAcc_work (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ)
    (cells : α → ℕ) (K : ℤ) (R L S : ℕ)
    (hr : ∀ s, (read s).2 ≤ R) (hk : ∀ x, (key x).2 ≤ L) (hs : ∀ x, cells x ≤ S)
    (fuel : ℕ) (s : σ) (buf : Array α) (q : ℕ) :
    (fillAcc read key cells K fuel s buf q).2 + (R + L + S + 8) * q ≤
      (R + L + S + 8) * (fillAcc read key cells K fuel s buf q).1.queries + 1 := by
  induction fuel generalizing s buf q with
  | zero => simp only [fillAcc]; omega
  | succ fuel ih =>
    have hread := hr s
    cases hv : (read s).1 with
    | none => simp only [fillAcc, hv, Nat.mul_add, Nat.mul_one]; omega
    | some z =>
      rcases z with ⟨x, s'⟩
      have hkey := hk x
      have hcell := hs x
      simp only [fillAcc, hv]
      split
      · have hrest := ih s' (buf.push x) (q + 1)
        simp only [Nat.mul_add, Nat.mul_one] at hrest
        dsimp only
        omega
      · simp only [Nat.mul_add, Nat.mul_one]; omega

def fill (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ)
    (cells : α → ℕ) (K : ℤ) (B : ℕ) (s : σ) : TieBuffer.Result α σ × ℕ :=
  fillAcc read key cells K B s #[] 0

theorem fill_value (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ)
    (cells : α → ℕ) (K : ℤ) (B : ℕ) (s : σ) :
    (fill read key cells K B s).1 =
      TieBuffer.fill (fun s => (read s).1) (fun x => (key x).1) K B s :=
  fillAcc_value _ _ _ _ _ _ _ _

theorem fill_work (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ)
    (cells : α → ℕ) (K : ℤ) (R L S : ℕ)
    (hr : ∀ s, (read s).2 ≤ R) (hk : ∀ x, (key x).2 ≤ L) (hs : ∀ x, cells x ≤ S)
    (B : ℕ) (s : σ) :
    (fill read key cells K B s).2 ≤
      (R + L + S + 8) * (fill read key cells K B s).1.queries + 1 := by
  simpa only [fill, Nat.mul_zero, Nat.add_zero] using
    fillAcc_work read key cells K R L S hr hk hs B s #[] 0

def hasKey (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ) (s : σ) : Bool × ℕ :=
  let fetched := read s
  match fetched.1 with
  | none => (false, fetched.2 + 3)
  | some (x, _) =>
    let found := key x
    (decide (found.1 = K), fetched.2 + found.2 + 4)

theorem hasKey_value (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ) (s : σ) :
    (hasKey read key K s).1 = TieBuffer.hasKey (fun s => (read s).1) (fun x => (key x).1) K s := by
  cases hv : (read s).1 <;> simp [hasKey, TieBuffer.hasKey, hv]

theorem hasKey_work (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (R L : ℕ) (hr : ∀ s, (read s).2 ≤ R) (hk : ∀ x, (key x).2 ≤ L) (s : σ) :
    (hasKey read key K s).2 ≤ R + L + 4 := by
  have hread := hr s
  cases hv : (read s).1 with
  | none => simp only [hasKey, hv]; omega
  | some z =>
    rcases z with ⟨x, s'⟩
    have hkey := hk x
    simp only [hasKey, hv]
    omega

end LowSpaceSubsetSum.CountedFill

end OAI
