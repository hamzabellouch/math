import OAI.Combinatorics.ContingencyTables.Transport.AffinePenalty
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field

namespace OAI

/-!
# Free coordinates of a dense completion block

`none` denotes the pivot row or column. The free coordinates are the other
cells. These are the manuscript's actual affine completion formulas; the
row and column constraints hold identically, and feasible tables are
uniquely determined by their free cells.
-/

namespace ContingencyTables.DenseAffine

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

def table (R : Option I → ℝ) (P : Option J → ℝ) (w : I → J → ℝ)
    (u : I × J → ℝ) : Option I → Option J → ℝ
  | some i, some j => w i j * u (i, j)
  | some i, none => R (some i) - ∑ j, w i j * u (i, j)
  | none, some j => P (some j) - ∑ i, w i j * u (i, j)
  | none, none => R none - ∑ j, P (some j) + ∑ i, ∑ j, w i j * u (i, j)

theorem table_rows (R : Option I → ℝ) (P : Option J → ℝ) (w : I → J → ℝ)
    (u : I × J → ℝ) (i : Option I) : ∑ j, table R P w u i j = R i := by
  rw [Fintype.sum_option]
  cases i with
  | some i => simp only [table]; ring
  | none =>
    simp only [table, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun i j => w i j * u (i, j))]
    ring

theorem table_columns (R : Option I → ℝ) (P : Option J → ℝ) (w : I → J → ℝ)
    (u : I × J → ℝ) (htotal : ∑ i, R i = ∑ j, P j) (j : Option J) :
    ∑ i, table R P w u i j = P j := by
  rw [Fintype.sum_option]
  cases j with
  | some j => simp only [table]; ring
  | none =>
    simp only [table, Finset.sum_sub_distrib]
    simp only [Fintype.sum_option] at htotal
    linarith

theorem table_unique (X Y : Option I → Option J → ℝ)
    (hrows : ∀ i, ∑ j, X i j = ∑ j, Y i j)
    (hcols : ∀ j, ∑ i, X i j = ∑ i, Y i j)
    (hfree : ∀ i j, X (some i) (some j) = Y (some i) (some j)) : X = Y := by
  have hr (i : I) : X (some i) none = Y (some i) none := by
    have h := hrows (some i)
    simp only [Fintype.sum_option, hfree] at h
    linarith
  have hc (j : J) : X none (some j) = Y none (some j) := by
    have h := hcols (some j)
    simp only [Fintype.sum_option, hfree] at h
    linarith
  have hnn : X none none = Y none none := by
    have h := hrows none
    simp only [Fintype.sum_option, hc] at h
    linarith
  funext i j
  cases i <;> cases j
  · exact hnn
  · exact hc _
  · exact hr _
  · exact hfree _ _

/-- Recover an actual table from its scaled free coordinates. -/
theorem table_recover (R : Option I → ℝ) (P : Option J → ℝ) (w : I → J → ℝ)
    (hw : ∀ i j, w i j ≠ 0) (X : Option I → Option J → ℝ)
    (hR : ∀ i, ∑ j, X i j = R i) (hP : ∀ j, ∑ i, X i j = P j) :
    table R P w (fun p => X (some p.1) (some p.2) / w p.1 p.2) = X := by
  have htotal : ∑ i, R i = ∑ j, P j := by
    simp_rw [← hR, ← hP]
    exact Finset.sum_comm
  apply table_unique
  · intro i
    rw [table_rows, hR]
  · intro j
    rw [table_columns _ _ _ _ htotal, hP]
  · intro i j
    simp only [table]
    exact mul_div_cancel₀ _ (hw i j)

end ContingencyTables.DenseAffine

end OAI
