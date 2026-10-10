import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceZeroFilter
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceMatrix

namespace OAI

/-! Complete matrix semantics for the literal bond registers. Removing zero
terms preserves the actual Hamiltonian, while valid bounded indices give
the exact finite family used in the mediator comparison. -/

noncomputable section
namespace ContinuumCoulomb.SourceBondLists
open Matrix MediatorIteration MediatorListProgram
open scoped BigOperators

def bondMatrix (n : ℕ) (e : Bond) : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  if h : e.1 < n ∧ e.2.1 < n then (e.2.2 : ℂ) •
    sourceHeisenbergMatrix n ⟨e.1, h.1⟩ ⟨e.2.1, h.2⟩ else 0

def matrix (n : ℕ) (xs : List Bond) : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  (xs.map (bondMatrix n)).sum

theorem bondMatrix_zero (n : ℕ) (e : Bond) (he : e.2.2 = 0) : bondMatrix n e = 0 := by
  unfold bondMatrix
  split <;> simp only [he, Rat.cast_zero, zero_smul]

theorem filter_matrix (n : ℕ) (xs : List Bond) :
    matrix n (xs.filter SourceZeroFilter.keep) = matrix n xs := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    by_cases h : e.2.2 = 0
    · have hk : ¬SourceZeroFilter.keep e := by simp [SourceZeroFilter.keep, h]
      rw [List.filter_cons_of_neg hk]
      simp only [matrix, List.map_cons, List.sum_cons, bondMatrix_zero n e h, zero_add] at *
      exact ih
    · have hk : SourceZeroFilter.keep e := by simp [SourceZeroFilter.keep, h]
      rw [List.filter_cons_of_pos hk]
      simp only [matrix, List.map_cons, List.sum_cons] at *
      rw [ih]

def bounded (n : ℕ) (xs : List Bond) : Prop := ∀ e ∈ xs, e.1 < n ∧ e.2.1 < n

def bonds (n : ℕ) (xs : List Bond) (h : bounded n xs) : Bonds n xs.length where
  left i := ⟨(xs.get i).1, (h _ (List.get_mem xs i)).1⟩
  right i := ⟨(xs.get i).2.1, (h _ (List.get_mem xs i)).2⟩
  weight i := (xs.get i).2.2

theorem matrix_bonds (n : ℕ) (xs : List Bond) (h : bounded n xs) :
    matrix n xs = (bonds n xs h).matrix := by
  have hlist : xs.map (bondMatrix n) = List.ofFn (fun i : Fin xs.length => bondMatrix n (xs.get i)) := by
    simpa only [List.get_eq_getElem] using (List.ofFn_getElem_eq_map xs (bondMatrix n)).symm
  rw [matrix, hlist, List.sum_ofFn]
  unfold Bonds.matrix sourceGraphMatrix
  apply Finset.sum_congr rfl
  intro i _
  rw [bondMatrix, dite_eq_left (h _ (List.get_mem xs i))]
  simp only [bonds, Complex.ofReal_ratCast]

theorem filter_bounded (n : ℕ) (xs : List Bond) (h : bounded n xs) :
    bounded n (xs.filter SourceZeroFilter.keep) := by
  intro e he
  exact h e (List.mem_filter.mp he).1

theorem bonds_noLoops (n : ℕ) (xs : List Bond) (h : bounded n xs)
    (hloop : ∀ e ∈ xs, e.1 ≠ e.2.1) : (bonds n xs h).NoLoops := by
  intro i hi
  exact hloop _ (List.get_mem xs i) (congrArg Fin.val hi)

end ContinuumCoulomb.SourceBondLists

end

end OAI
