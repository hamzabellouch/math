import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordTuple

namespace OAI

/-! # Finite fair-word streams realize the sequential operational law -/

noncomputable section
namespace LowSpaceSubsetSum.WordProgram

open scoped BigOperators
variable {w : ℕ} {α : Type}

def finiteStream {N : ℕ} (words : Fin N → Fin (2^w)) (i : ℕ) : Fin (2^w) :=
  if h : i < N then words ⟨i,h⟩ else 0

theorem run_shift (stream : ℕ → Fin (2^w)) (p : Program w α) (offset k : ℕ) :
    run stream p (offset+k) =
      let out := run (fun i => stream (i+k)) p offset
      (out.1,out.2+k) := by
  induction p generalizing offset with
  | pure a => rfl
  | draw branch ih =>
    simp only [run]
    simpa only [Nat.add_assoc, Nat.add_comm k 1, Nat.add_left_comm] using
      ih (stream (offset+k)) (offset+1)

theorem finiteStream_cons (x : Fin (2^w)) {N : ℕ} (xs : Fin N → Fin (2^w)) :
    (fun i => finiteStream (Fin.cons x xs) (i+1)) = finiteStream xs := by
  funext i
  unfold finiteStream
  by_cases h : i < N
  · simp only [show i+1 < N+1 by omega, ↓reduceDIte, h]
    change Fin.cons (n := N) (α := fun _ => Fin (2^w)) x xs (Fin.succ ⟨i,h⟩) = xs ⟨i,h⟩
    rfl
  · simp only [show ¬i+1 < N+1 by omega, ↓reduceDIte, h]

theorem draw_cons_value (branch : Fin (2^w) → Program w α) {N : ℕ}
    (x : Fin (2^w)) (xs : Fin N → Fin (2^w)) :
    (run (finiteStream (Fin.cons x xs)) (.draw branch) 0).1 =
      (run (finiteStream xs) (branch x) 0).1 := by
  have hzero : finiteStream (Fin.cons x xs) 0 = x := by
    simp [finiteStream]
  simp only [run, hzero, Nat.zero_add]
  have h := congrArg Prod.fst (run_shift (finiteStream (Fin.cons x xs)) (branch x) 0 1)
  simpa only [Nat.zero_add, finiteStream_cons] using h

theorem run_expectation (p : Program w α) (N : ℕ) (hp : Bounded p N) (f : α → ℝ) :
    expectation p f = (FiniteLaw.uniform : FiniteLaw (Fin N → Fin (2^w))).expectation
      (fun words => f (run (finiteStream words) p 0).1) := by
  induction hp with
  | pure a N =>
    simp only [expectation, run, FiniteLaw.expectation, ← Finset.sum_mul,
      FiniteLaw.total, one_mul]
  | draw branch N hb ih =>
    rw [WordTuple.cons_expectation]
    simp only [expectation, draw_cons_value, ih]

theorem run_probability (p : Program w α) (N : ℕ) (hp : Bounded p N) (P : α → Prop) :
    probability p P = (FiniteLaw.uniform : FiniteLaw (Fin N → Fin (2^w))).probability
      (fun words => P (run (finiteStream words) p 0).1) := by
  rw [probability, run_expectation p N hp, FiniteLaw.probability_eq_expectation]

end LowSpaceSubsetSum.WordProgram

end

end OAI
