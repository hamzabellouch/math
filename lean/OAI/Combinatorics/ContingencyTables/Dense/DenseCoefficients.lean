import OAI.Combinatorics.ContingencyTables.Dense.DenseAffine

namespace OAI

/-!
# Coefficients of normalized dense entries

Reordering maximum margins to the pivot makes each contributing free-cell
scale no larger than the dependent-cell scale. Thus every normalized
coefficient is bounded by `1/B`, as required by the actual penalty proof.
-/

namespace ContingencyTables.DenseAffine

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def entryOffset (R : Option I → ℝ) (P : Option J → ℝ) : Option I × Option J → ℝ
  | (some _, some _) => 0
  | (some i, none) => R (some i)
  | (none, some j) => P (some j)
  | (none, none) => R none - ∑ j, P (some j)

def entryCoeff (w : I → J → ℝ) : (Option I × Option J) → (I × J) → ℝ
  | (some i, some j), p => if p = (i, j) then w i j else 0
  | (some i, none), p => if p.1 = i then -w p.1 p.2 else 0
  | (none, some j), p => if p.2 = j then -w p.1 p.2 else 0
  | (none, none), p => w p.1 p.2

theorem table_affine (R : Option I → ℝ) (P : Option J → ℝ) (w : I → J → ℝ)
    (u : I × J → ℝ) (g : Option I × Option J) :
    table R P w u g.1 g.2 =
      AffinePenalty.affineValue (entryOffset R P g) (entryCoeff w g) u := by
  rcases g with ⟨i, j⟩
  cases i <;> cases j
  · simp [table, AffinePenalty.affineValue, entryOffset, entryCoeff, Fintype.sum_prod_type]
  · simp [table, AffinePenalty.affineValue, entryOffset, entryCoeff,
      Fintype.sum_prod_type, ite_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  · simp [table, AffinePenalty.affineValue, entryOffset, entryCoeff,
      Fintype.sum_prod_type, ite_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  · simp [table, AffinePenalty.affineValue, entryOffset, entryCoeff, ite_mul]

def cellScale (R : Option I → ℝ) (P : Option J → ℝ)
    (g : Option I × Option J) : ℝ := min (R g.1) (P g.2)

omit [Fintype I] [Fintype J] in
theorem entryCoeff_bound (R : Option I → ℝ) (P : Option J → ℝ) (w : I → J → ℝ)
    (B : ℝ) (hB : 0 < B)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hw : ∀ i j, 0 ≤ w i j)
    (hwidth : ∀ i j, w i j ≤ cellScale R P (some i, some j) / B)
    (hscale : ∀ g, 0 ≤ cellScale R P g) (g : Option I × Option J) (p : I × J) :
    |entryCoeff w g p| ≤ cellScale R P g / B := by
  rcases g with ⟨i, j⟩
  cases i with
  | none =>
    cases j with
    | none =>
      simp only [entryCoeff, abs_of_nonneg (hw p.1 p.2)]
      exact (hwidth p.1 p.2).trans (div_le_div_of_nonneg_right
        (min_le_min (hRmax p.1) (hPmax p.2)) hB.le)
    | some j =>
      by_cases hp : p.2 = j
      · simp only [entryCoeff, hp, ite_true, abs_neg, abs_of_nonneg (hw p.1 j)]
        exact (hwidth p.1 j).trans (div_le_div_of_nonneg_right
          (min_le_min_right _ (hRmax p.1)) hB.le)
      · simp only [entryCoeff, hp, ite_false, abs_zero]
        exact div_nonneg (hscale _) hB.le
  | some i =>
    cases j with
    | none =>
      by_cases hp : p.1 = i
      · simp only [entryCoeff, hp, ite_true, abs_neg, abs_of_nonneg (hw i p.2)]
        exact (hwidth i p.2).trans (div_le_div_of_nonneg_right
          (min_le_min_left _ (hPmax p.2)) hB.le)
      · simp only [entryCoeff, hp, ite_false, abs_zero]
        exact div_nonneg (hscale _) hB.le
    | some j =>
      by_cases hp : p = (i, j)
      · simp only [entryCoeff, hp, ite_true, abs_of_nonneg (hw i j)]
        exact hwidth i j
      · simp only [entryCoeff, hp, ite_false, abs_zero]
        exact div_nonneg (hscale _) hB.le

theorem normalized_table_affine (R : Option I → ℝ) (P : Option J → ℝ)
    (w : I → J → ℝ) (u : I × J → ℝ) (g : Option I × Option J) :
    table R P w u g.1 g.2 / cellScale R P g =
      AffinePenalty.affineValue (entryOffset R P g / cellScale R P g)
        (fun p => entryCoeff w g p / cellScale R P g) u := by
  rw [table_affine]
  unfold AffinePenalty.affineValue
  rw [add_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  ring

omit [Fintype I] [Fintype J] in
theorem normalized_coeff_bound (R : Option I → ℝ) (P : Option J → ℝ)
    (w : I → J → ℝ) (B : ℝ) (hB : 0 < B)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hw : ∀ i j, 0 ≤ w i j)
    (hwidth : ∀ i j, w i j ≤ cellScale R P (some i, some j) / B)
    (hscale : ∀ g, 0 < cellScale R P g) (g : Option I × Option J) (p : I × J) :
    |entryCoeff w g p / cellScale R P g| ≤ 1 / B := by
  rw [abs_div, abs_of_pos (hscale g)]
  calc
    _ ≤ (cellScale R P g / B) / cellScale R P g :=
      div_le_div_of_nonneg_right (entryCoeff_bound R P w B hB hRmax hPmax hw hwidth
        (fun g => (hscale g).le) g p) (hscale g).le
    _ = 1 / B := by field_simp [ne_of_gt (hscale g), ne_of_gt hB]

end ContingencyTables.DenseAffine

end OAI
