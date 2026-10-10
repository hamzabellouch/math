import OAI.Combinatorics.LowSpaceSubsetSum.Counting.ExactWordDraw

namespace OAI

/-! # Sequential fair-word programs for the bounded samplers

A draw reads one fresh word. Continuations are evaluated only after that
word is read. The finite expectation is the operational probability law;
there are no eligible-backup draws in this interface.
-/

namespace LowSpaceSubsetSum.WordProgram

open scoped BigOperators
attribute [local instance] Classical.propDecidable

inductive Program (w : ℕ) (α : Type) where
  | pure : α → Program w α
  | draw : (Fin (2^w) → Program w α) → Program w α

variable {w : ℕ} {α β : Type}

def bind : Program w α → (α → Program w β) → Program w β
  | .pure a, next => next a
  | .draw next, tail => .draw (fun x => bind (next x) tail)

def map (f : α → β) (p : Program w α) : Program w β := bind p (fun a => .pure (f a))

noncomputable def expectation : Program w α → (α → ℝ) → ℝ
  | .pure a, f => f a
  | .draw next, f => (∑ x, expectation (next x) f) / (2^w : ℕ)

noncomputable def probability (p : Program w α) (P : α → Prop) : ℝ :=
  expectation p (fun a => if P a then 1 else 0)

theorem expectation_bind (p : Program w α) (next : α → Program w β) (f : β → ℝ) :
    expectation (bind p next) f = expectation p (fun a => expectation (next a) f) := by
  induction p with
  | pure a => rfl
  | draw branch ih =>
    simp only [bind, expectation, ih]

theorem probability_map (f : α → β) (p : Program w α) (P : β → Prop) :
    probability (map f p) P = probability p (fun a => P (f a)) := by
  simp only [map, probability, expectation_bind, expectation]

theorem expectation_sum {ι : Type} [Fintype ι] (p : Program w α) (f : ι → α → ℝ) :
    expectation p (fun a => ∑ i, f i a) = ∑ i, expectation p (f i) := by
  induction p with
  | pure a => rfl
  | draw branch ih =>
    simp only [expectation, ih]
    rw [Finset.sum_comm, Finset.sum_div]

theorem expectation_mul (p : Program w α) (f : α → ℝ) (c : ℝ) :
    expectation p (fun a => f a*c) = expectation p f*c := by
  induction p with
  | pure a => rfl
  | draw branch ih =>
    simp only [expectation, ih, ← Finset.sum_mul]
    ring

theorem expectation_eq_sum [Fintype α] (p : Program w α) (f : α → ℝ) :
    expectation p f = ∑ a, probability p (fun x => x=a)*f a := by
  classical
  calc
    expectation p f = expectation p (fun x => ∑ a, (if x=a then 1 else 0)*f a) := by
      congr 1
      funext x
      simp
    _ = ∑ a, expectation p (fun x => (if x=a then 1 else 0)*f a) := expectation_sum p _
    _ = _ := by simp only [expectation_mul, probability]

theorem expectation_of_probability [Fintype α] (p : Program w α) (μ : FiniteLaw α)
    (h : ∀ P, probability p P = μ.probability P) (f : α → ℝ) :
    expectation p f = μ.expectation f := by
  rw [expectation_eq_sum]
  simp only [h, FiniteLaw.probability_eq, FiniteLaw.expectation]

theorem expectation_const (p : Program w α) (c : ℝ) : expectation p (fun _ => c) = c := by
  induction p with
  | pure a => rfl
  | draw branch ih =>
    simp only [expectation, ih, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have h : ((2^w : ℕ) : ℝ) ≠ 0 := by positivity
    exact mul_div_cancel_left₀ c h

theorem probability_true (p : Program w α) : probability p (fun _ => True) = 1 := by
  simp only [probability, ↓reduceIte]
  exact expectation_const p 1

theorem expectation_nonneg (p : Program w α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    0 ≤ expectation p f := by
  induction p with
  | pure a => exact hf a
  | draw branch ih =>
    exact div_nonneg (Finset.sum_nonneg (fun x _ => ih x)) (by positivity)

theorem expectation_mono (p : Program w α) (f g : α → ℝ) (h : ∀ a, f a ≤ g a) :
    expectation p f ≤ expectation p g := by
  induction p with
  | pure a => exact h a
  | draw branch ih =>
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => ih x)) (by positivity)

/-- A read-only random stream supplies the words in order. -/
def run (stream : ℕ → Fin (2^w)) : Program w α → ℕ → α × ℕ
  | .pure a, offset => (a, offset)
  | .draw next, offset => run stream (next (stream offset)) (offset+1)

/-- A structural draw bound, independent of the stream's values. -/
inductive Bounded : Program w α → ℕ → Prop where
  | pure (a : α) (N : ℕ) : Bounded (.pure a) N
  | draw (next : Fin (2^w) → Program w α) (N : ℕ)
      (bound : ∀ x, Bounded (next x) N) : Bounded (.draw next) (N+1)

theorem run_bound (p : Program w α) (N : ℕ) (h : Bounded p N)
    (stream : ℕ → Fin (2^w)) (offset : ℕ) :
    offset ≤ (run stream p offset).2 ∧ (run stream p offset).2 ≤ offset+N := by
  induction h generalizing offset with
  | pure a N => exact ⟨le_rfl, Nat.le_add_right _ _⟩
  | draw next N bound ih =>
    have ht := ih (stream offset) (offset+1)
    change offset ≤ (run stream (next (stream offset)) (offset+1)).2 ∧
      (run stream (next (stream offset)) (offset+1)).2 ≤ offset+(N+1)
    omega

theorem bound_add (p : Program w α) (M : ℕ) (hp : Bounded p M) (N : ℕ) :
    Bounded p (N+M) := by
  induction hp with
  | pure a M => exact Bounded.pure a (N+M)
  | draw branch M hb ih =>
    simpa only [Nat.add_assoc] using Bounded.draw branch (N+M) ih

theorem bind_bound (p : Program w α) (N : ℕ) (hp : Bounded p N)
    (next : α → Program w β) (M : ℕ) (hn : ∀ a, Bounded (next a) M) :
    Bounded (bind p next) (N+M) := by
  induction hp with
  | pure a N => exact bound_add (next a) M (hn a) N
  | draw branch N hb ih =>
    simpa only [bind, Nat.add_assoc, Nat.add_comm 1 M, Nat.add_left_comm] using
      Bounded.draw (fun x => bind (branch x) next) (N+M) ih

end LowSpaceSubsetSum.WordProgram

end OAI
