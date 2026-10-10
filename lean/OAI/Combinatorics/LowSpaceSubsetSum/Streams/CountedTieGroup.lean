import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedFill
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CountedJoinOne
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedReplayPotential
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.TieGroup

namespace OAI

/-! # Counted Cartesian tie groups with telescoping replay costs -/

namespace LowSpaceSubsetSum.CountedTieGroup

universe u v s t w
variable {α : Type u} {β : Type v} {σ₁ : Type s} {σ₂ : Type t} {τ : Type w}

def potential (A C B : ℕ) (st : TieGroup.State σ₂ τ) : ℕ :=
  A * st.queries + C * st.reports + B * st.restores

def step (read : σ₂ → Option (β × σ₂) × ℕ) (key : β → ℤ × ℕ) (K : ℤ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (buffer : Array β) (saved : σ₂) (long : Bool) (fuel : ℕ)
    (x : α) (st : TieGroup.State σ₂ τ) : (TieGroup.State σ₂ τ × Bool) × ℕ :=
  let out := CountedJoinOne.run read key K (report x) clone buffer saved long fuel st.user
  ((⟨out.1.cursor, out.1.state, st.queries + out.1.queries, st.reports + out.1.reports,
      st.restores + if long then 1 else 0⟩, out.1.halted), out.2 + 6)

theorem step_value (read : σ₂ → Option (β × σ₂) × ℕ) (key : β → ℤ × ℕ) (K : ℤ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (hclone : ∀ s, (clone s).1 = s) (buffer : Array β) (saved : σ₂)
    (long : Bool) (fuel : ℕ) (x : α) (st : TieGroup.State σ₂ τ) :
    (step read key K report clone buffer saved long fuel x st).1 =
      TieGroup.step (fun s => (read s).1) (fun y => (key y).1) K
        (fun x y a => (report x y a).1) buffer saved long fuel x st := by
  simp only [step, CountedJoinOne.run_value read key K (report x) clone hclone, TieGroup.step]

theorem step_work_potential
    (read : σ₂ → Option (β × σ₂) × ℕ) (key : β → ℤ × ℕ) (K : ℤ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (R L C B : ℕ) (hr : ∀ s, (read s).2 ≤ R) (hk : ∀ y, (key y).2 ≤ L)
    (hc : ∀ x y a, (report x y a).2 ≤ C) (hcopy : ∀ s, (clone s).2 ≤ B)
    (buffer : Array β) (saved : σ₂) (long : Bool) (fuel : ℕ) (x : α) (st : TieGroup.State σ₂ τ) :
    (step read key K report clone buffer saved long fuel x st).2 +
        potential (max R 4 + L + 8) C B st ≤
      potential (max R 4 + L + 8) C B
        (step read key K report clone buffer saved long fuel x st).1.1 + 13 := by
  have h := CountedJoinOne.run_work read key K (report x) clone R L C B hr hk (hc x) hcopy
    buffer saved long fuel st.user
  cases long <;> simp only [step, potential, Bool.false_eq_true, ↓reduceIte,
    Nat.mul_add, Nat.mul_one, Nat.add_zero] at h ⊢ <;> omega

def run (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ) (cells : β → ℕ) (K : ℤ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (B fuel₁ fuel₂ : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ) : TieGroup.Result σ₁ σ₂ τ × ℕ :=
  let filled := CountedFill.fill read₂ key₂ cells K B s₂
  let long := CountedFill.hasKey read₂ key₂ K filled.1.cursor
  let left := CountedFill.hasKey read₁ key₁ K s₁
  let saved := if long.1 && left.1 then clone filled.1.cursor else (filled.1.cursor, 0)
  let out := CountedReplay.run read₁ key₁ K
    (step read₂ key₂ K report clone filled.1.buffer saved.1 long.1 fuel₂)
    fuel₁ s₁ ⟨filled.1.cursor, a, 0, 0, 0⟩
  (⟨out.1, filled.1.queries, filled.1.buffer.size, long.1 && left.1⟩,
    filled.2 + long.2 + left.2 + saved.2 + out.2 + 8)

theorem run_value (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ) (cells : β → ℕ) (K : ℤ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (hclone : ∀ s, (clone s).1 = s) (B fuel₁ fuel₂ : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ) :
    (run read₁ key₁ read₂ key₂ cells K report clone B fuel₁ fuel₂ s₁ s₂ a).1 =
      TieGroup.run (fun s => (read₁ s).1) (fun x => (key₁ x).1)
        (fun s => (read₂ s).1) (fun y => (key₂ y).1) K
        (fun x y a => (report x y a).1) B fuel₁ fuel₂ s₁ s₂ a := by
  have hc : ∀ b : Bool, ∀ s, (if b then clone s else (s, 0)).1 = s := by
    intro b s
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, hclone]
  simp only [run, hc, CountedReplay.run_value, step_value read₂ key₂ K report clone hclone,
    CountedFill.fill_value, CountedFill.hasKey_value, TieGroup.run]

/-- The group cost follows its exact query, report and copy ledger. In
particular, suffix fuel is not multiplied by the number of outer records. -/
theorem run_work
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ) (cells : β → ℕ) (K : ℤ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (R₁ R₂ L₁ L₂ S C D : ℕ)
    (hr₁ : ∀ s, (read₁ s).2 ≤ R₁) (hr₂ : ∀ s, (read₂ s).2 ≤ R₂)
    (hk₁ : ∀ x, (key₁ x).2 ≤ L₁) (hk₂ : ∀ y, (key₂ y).2 ≤ L₂)
    (hs : ∀ y, cells y ≤ S) (hc : ∀ x y a, (report x y a).2 ≤ C)
    (hcopy : ∀ s, (clone s).2 ≤ D)
    (B fuel₁ fuel₂ : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ) :
    (run read₁ key₁ read₂ key₂ cells K report clone B fuel₁ fuel₂ s₁ s₂ a).2 ≤
      (R₁ + R₂ + L₁ + L₂ + S + 50) *
        ((run read₁ key₁ read₂ key₂ cells K report clone B fuel₁ fuel₂ s₁ s₂ a).1.outer.queries +
         (run read₁ key₁ read₂ key₂ cells K report clone B fuel₁ fuel₂ s₁ s₂ a).1.fillQueries +
         (run read₁ key₁ read₂ key₂ cells K report clone B fuel₁ fuel₂ s₁ s₂ a).1.outer.state.queries + 1) +
      C * (run read₁ key₁ read₂ key₂ cells K report clone B fuel₁ fuel₂ s₁ s₂ a).1.outer.state.reports +
      D * ((if (run read₁ key₁ read₂ key₂ cells K report clone B fuel₁ fuel₂ s₁ s₂ a).1.snapshot then 1 else 0) +
        (run read₁ key₁ read₂ key₂ cells K report clone B fuel₁ fuel₂ s₁ s₂ a).1.outer.state.restores) := by
  let filled := CountedFill.fill read₂ key₂ cells K B s₂
  let long := CountedFill.hasKey read₂ key₂ K filled.1.cursor
  let left := CountedFill.hasKey read₁ key₁ K s₁
  let saved := if long.1 && left.1 then clone filled.1.cursor else (filled.1.cursor, 0)
  let f := step read₂ key₂ K report clone filled.1.buffer saved.1 long.1 fuel₂
  let out := CountedReplay.run read₁ key₁ K f fuel₁ s₁ ⟨filled.1.cursor, a, 0, 0, 0⟩
  let A := max R₂ 4 + L₂ + 8
  let M := R₁ + R₂ + L₁ + L₂ + S + 50
  have hp : ∀ x st, (f x st).2 + potential A C D st ≤
      potential A C D (f x st).1.1 + 13 := by
    intro x st
    exact step_work_potential read₂ key₂ K report clone R₂ L₂ C D hr₂ hk₂ hc hcopy
      filled.1.buffer saved.1 long.1 fuel₂ x st
  have ho := CountedReplay.run_work_potential read₁ key₁ K f (potential A C D)
    R₁ L₁ 13 hr₁ hk₁ hp fuel₁ s₁ ⟨filled.1.cursor, a, 0, 0, 0⟩
  change out.2 + potential A C D ⟨filled.1.cursor, a, 0, 0, 0⟩ ≤
    (R₁ + L₁ + 13 + 8) * out.1.queries + potential A C D out.1.state + 1 at ho
  simp only [potential, Nat.mul_zero, Nat.add_zero] at ho
  have hf := CountedFill.fill_work read₂ key₂ cells K R₂ L₂ S hr₂ hk₂ hs B s₂
  change filled.2 ≤ (R₂ + L₂ + S + 8) * filled.1.queries + 1 at hf
  have hl := CountedFill.hasKey_work read₂ key₂ K R₂ L₂ hr₂ hk₂ filled.1.cursor
  change long.2 ≤ R₂ + L₂ + 4 at hl
  have hleft := CountedFill.hasKey_work read₁ key₁ K R₁ L₁ hr₁ hk₁ s₁
  change left.2 ≤ R₁ + L₁ + 4 at hleft
  have hsaved : saved.2 ≤ D * (if long.1 && left.1 then 1 else 0) := by
    dsimp only [saved]
    split
    · simpa only [Nat.mul_one] using hcopy filled.1.cursor
    · simp
  have houter := Nat.mul_le_mul_right out.1.queries
    (show R₁ + L₁ + 13 + 8 ≤ M by dsimp only [M]; omega)
  have hfill := Nat.mul_le_mul_right filled.1.queries
    (show R₂ + L₂ + S + 8 ≤ M by dsimp only [M]; omega)
  have hinner := Nat.mul_le_mul_right out.1.state.queries
    (show A ≤ M by dsimp only [A, M]; omega)
  change filled.2 + long.2 + left.2 + saved.2 + out.2 + 8 ≤
    M * (out.1.queries + filled.1.queries + out.1.state.queries + 1) +
      C * out.1.state.reports + D * ((if long.1 && left.1 then 1 else 0) + out.1.state.restores)
  simp only [Nat.mul_add, Nat.mul_one]
  dsimp only [M] at houter hfill hinner ⊢
  omega

end LowSpaceSubsetSum.CountedTieGroup

end OAI
