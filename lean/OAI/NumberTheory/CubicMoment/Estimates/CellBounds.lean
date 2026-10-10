import Mathlib

namespace OAI

/-!
# Two-variable localization bounds

The finite inequalities underlying `eq:near-cell-diagonal`,
`eq:all-cell-error`, and `eq:far-cell-diagonal` in the sharp-cutoff argument.
The incidence set records which pairs of norm cells meet the product boundary.
Both row and column degrees enter the near-boundary bound.
-/

noncomputable section
open scoped BigOperators

namespace CubicFirstMoment

/-- Counting a cell's energy once for each of its incident pairs costs at
most the degree bound. -/
theorem cell_incidence_energy {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (E : Finset (ι × κ)) (a : ι → ℝ) (D : ℕ)
    (hI : ∀ e ∈ E, e.1 ∈ I)
    (hD : ∀ i ∈ I, (E.filter (fun e => e.1 = i)).card ≤ D) :
    (∑ e ∈ E, (a e.1) ^ 2) ≤ (D : ℝ) * ∑ i ∈ I, (a i) ^ 2 := by
  rw [← Finset.sum_fiberwise_of_maps_to hI (fun e => (a e.1) ^ 2), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    (∑ e ∈ E.filter (fun e => e.1 = i), (a e.1) ^ 2) =
        ((E.filter (fun e => e.1 = i)).card : ℝ) * (a i) ^ 2 := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro e he
      rw [(Finset.mem_filter.mp he).2]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hD i hi) (sq_nonneg _)

/-- The corresponding column-energy bound. -/
theorem cell_incidence_energy_right {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (J : Finset κ) (E : Finset (ι × κ)) (b : κ → ℝ) (D : ℕ)
    (hJ : ∀ e ∈ E, e.2 ∈ J)
    (hD : ∀ j ∈ J, (E.filter (fun e => e.2 = j)).card ≤ D) :
    (∑ e ∈ E, (b e.2) ^ 2) ≤ (D : ℝ) * ∑ j ∈ J, (b j) ^ 2 := by
  rw [← Finset.sum_fiberwise_of_maps_to hJ (fun e => (b e.2) ^ 2), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  calc
    (∑ e ∈ E.filter (fun e => e.2 = j), (b e.2) ^ 2) =
        ((E.filter (fun e => e.2 = j)).card : ℝ) * (b j) ^ 2 := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro e he
      rw [(Finset.mem_filter.mp he).2]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hD j hj) (sq_nonneg _)

/-- Localizing both variables gives the bounded-degree Cauchy inequality.
Only the near pairs are summed, rather than all pairs of cells. -/
theorem near_cell_sum_sq {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (J : Finset κ) (E : Finset (ι × κ))
    (a : ι → ℝ) (b : κ → ℝ) (D : ℕ)
    (hI : ∀ e ∈ E, e.1 ∈ I) (hJ : ∀ e ∈ E, e.2 ∈ J)
    (hrow : ∀ i ∈ I, (E.filter (fun e => e.1 = i)).card ≤ D)
    (hcol : ∀ j ∈ J, (E.filter (fun e => e.2 = j)).card ≤ D) :
    (∑ e ∈ E, a e.1 * b e.2) ^ 2 ≤
      (D : ℝ) ^ 2 * (∑ i ∈ I, (a i) ^ 2) * ∑ j ∈ J, (b j) ^ 2 := by
  have ha := cell_incidence_energy I E a D hI hrow
  have hb := cell_incidence_energy_right J E b D hJ hcol
  calc
    _ ≤ (∑ e ∈ E, (a e.1) ^ 2) * ∑ e ∈ E, (b e.2) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq E _ _
    _ ≤ ((D : ℝ) * ∑ i ∈ I, (a i) ^ 2) *
        ((D : ℝ) * ∑ j ∈ J, (b j) ^ 2) :=
      mul_le_mul ha hb (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    _ = _ := by ring

/-- Unsquaring the near-boundary estimate. The cell masses are L² norms
in the application and are thus nonnegative. -/
theorem near_cell_sum_le {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (J : Finset κ) (E : Finset (ι × κ))
    (a : ι → ℝ) (b : κ → ℝ) (D : ℕ)
    (hI : ∀ e ∈ E, e.1 ∈ I) (hJ : ∀ e ∈ E, e.2 ∈ J)
    (hrow : ∀ i ∈ I, (E.filter (fun e => e.1 = i)).card ≤ D)
    (hcol : ∀ j ∈ J, (E.filter (fun e => e.2 = j)).card ≤ D) :
    (∑ e ∈ E, a e.1 * b e.2) ≤
      (D : ℝ) * Real.sqrt (∑ i ∈ I, (a i) ^ 2) *
        Real.sqrt (∑ j ∈ J, (b j) ^ 2) := by
  have h := near_cell_sum_sq I J E a b D hI hJ hrow hcol
  have ha := Real.sq_sqrt (Finset.sum_nonneg (fun i (_ : i ∈ I) => sq_nonneg (a i)))
  have hb := Real.sq_sqrt (Finset.sum_nonneg (fun j (_ : j ∈ J) => sq_nonneg (b j)))
  have he : ((D : ℝ) * Real.sqrt (∑ i ∈ I, (a i) ^ 2) *
      Real.sqrt (∑ j ∈ J, (b j) ^ 2)) ^ 2 =
      (D : ℝ) ^ 2 * (∑ i ∈ I, (a i) ^ 2) * ∑ j ∈ J, (b j) ^ 2 := by
    rw [mul_pow, mul_pow, ha, hb]
  rw [← he] at h
  have hn : 0 ≤ (D : ℝ) * Real.sqrt (∑ i ∈ I, (a i) ^ 2) *
      Real.sqrt (∑ j ∈ J, (b j) ^ 2) := by positivity
  nlinarith

/-- Without a near-pair restriction, the sum of cell masses costs the
square root of the number of cells on each side. -/
theorem cell_mass_sum_sq {ι : Type*} (I : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ I, a i) ^ 2 ≤ (I.card : ℝ) * ∑ i ∈ I, (a i) ^ 2 := by
  simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
    Finset.sum_mul_sq_le_sq_mul_sq I (fun _ => (1 : ℝ)) a

/-- The absolute errors over all cell pairs lose three powers of the
square root of the number of cells, as in `eq:all-cell-error`. -/
theorem all_cell_error_sq {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (a : ι → ℝ) (error : ℝ) :
    (∑ i ∈ I, ∑ _j ∈ J, a i * error) ^ 2 ≤
      error ^ 2 * (J.card : ℝ) ^ 2 * (I.card : ℝ) * ∑ i ∈ I, (a i) ^ 2 := by
  have he : (∑ i ∈ I, ∑ _j ∈ J, a i * error) =
      (J.card : ℝ) * error * ∑ i ∈ I, a i := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, mul_pow]
  have h := mul_le_mul_of_nonneg_left (cell_mass_sum_sq I a)
    (sq_nonneg ((J.card : ℝ) * error))
  nlinarith only [h]

end CubicFirstMoment

end

end OAI
