import Mathlib
import OAI.Computability.QuantumFactoring.BooleanAlgebra

namespace OAI

section


open scoped BigOperators
namespace ExactQuantumFactoring.BooleanNetwork

/-- Assemble an arbitrary vector of single-bit combinational outputs, retaining
separate traces. This is a finite circuit construction, not a truth table. -/
def vector {n : ℕ} : {m : ℕ} → (Fin m → BooleanNetwork n 1) → BooleanNetwork n m
  | 0, _ => select Fin.elim0
  | m+1, f => (vector (fun i => f i.castSucc)).pair (f (Fin.last m))

@[simp] lemma eval_vector {n m : ℕ} (f : Fin m → BooleanNetwork n 1)
    (x : Fin n → Bool) (i : Fin m) : (vector f).eval x i = (f i).eval x 0 := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    rw [vector, eval_pair, Fin.append_right_eq_snoc]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_last]
    · rw [Fin.snoc_castSucc]
      exact ih _ j

@[simp] lemma count_vector {n m : ℕ} (f : Fin m → BooleanNetwork n 1) :
    (vector f).net.count = ∑ i, (f i).net.count := by
  induction m with
  | zero => simp [vector]
  | succ m ih => simp [vector, count_pair, ih, Fin.sum_univ_castSucc]

lemma count_vector_le {n m c : ℕ} (f : Fin m → BooleanNetwork n 1)
    (h : ∀ i, (f i).net.count ≤ c) : (vector f).net.count ≤ m*c := by
  rw [count_vector]
  calc
    _ ≤ ∑ _ : Fin m, c := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp

/-- Add explicit zero slots, with <=m nodes. Duplicate outputs may share zero,
but the simple linear upper bound is sufficient for the compiler. -/
def padRight (n m : ℕ) : BooleanNetwork n (n+m) :=
  vector (fun i => if h : i.val < n then bit ⟨i.val,h⟩ else constant false)

lemma eval_padRight (n m : ℕ) (x : Fin n → Bool) :
    (padRight n m).eval x = Fin.append x (fun _ => false) := by
  funext i
  rw [padRight, eval_vector]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [j.isLt]
  · simp

lemma count_padRight (n m : ℕ) : (padRight n m).net.count = m := by
  rw [padRight, count_vector, Fin.sum_univ_add]
  have h₁ : (∑ x : Fin n, (if h : x.val < n then bit (n := n) ⟨x.val,h⟩
      else constant false).net.count) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [dite_eq_left x.isLt]
    rfl
  have h₂ : (∑ x : Fin m, (if h : n+x.val < n then bit (n := n) ⟨n+x.val,h⟩
      else constant false).net.count) = m := by
    trans ∑ _ : Fin m, 1
    · apply Finset.sum_congr rfl
      intro x _
      rw [dite_eq_right (by omega : ¬ n+x.val < n)]
      rfl
    · simp
  exact (congrArg₂ (· + ·) h₁ h₂).trans (Nat.zero_add _)

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
