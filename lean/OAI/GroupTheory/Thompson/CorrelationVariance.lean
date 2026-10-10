import OAI.GroupTheory.Thompson.FiniteAverage
import OAI.GroupTheory.Thompson.HilbertAverage
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Exact finite correlation and variance estimates

The diagonal and off-diagonal coefficients are exact finite counts. The mixed
sum has one exceptional parent column, hence D nested terms and D(D-1)
separated terms. Every count identity permits arbitrary signed coefficients.
The final cancellation imposes no positivity assumption on the common
correlation alpha.
-/

noncomputable section

universe uG uE

namespace ThompsonNonamenability

open scoped BigOperators InnerProductSpace

variable {D : ℕ}

/-- One distinguished position and all the other positions, with signed values. -/
theorem sum_one_exception (i : Fin D) (b c : ℝ) :
    (∑ j : Fin D, if j = i then b else c) = b + ((D : ℝ) - 1) * c := by
  classical
  have hterm (j : Fin D) :
      (if j = i then b else c) = c + (if j = i then b - c else 0) := by
    by_cases h : j = i <;> simp [h]
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, Fintype.sum_ite_eq', Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- D diagonal terms and D(D-1) off-diagonal terms, with no sign premise. -/
theorem sum_matrix_le (K : Fin D → Fin D → ℝ) (b c : ℝ)
    (hdiag : ∀ j, K j j ≤ b)
    (hoff : ∀ j k, j ≠ k → K j k ≤ c) :
    (∑ j, ∑ k, K j k) ≤
      (D : ℝ) * ((D : ℝ) - 1) * c + (D : ℝ) * b := by
  classical
  calc
    (∑ j, ∑ k, K j k) ≤ ∑ j : Fin D, ∑ k : Fin D, if k = j then b else c := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      by_cases h : k = j
      · subst k
        simpa using hdiag j
      · simpa only [ite_eq_right h] using hoff j k (Ne.symm h)
    _ = (D : ℝ) * ((D : ℝ) - 1) * c + (D : ℝ) * b := by
      simp_rw [sum_one_exception]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The exceptional column contributes D terms, irrespective of the row index. -/
theorem sum_fixed_column_ge (i : Fin D) (K : Fin D → Fin D → ℝ) (b c : ℝ)
    (hnested : ∀ j, b ≤ K j i)
    (hsep : ∀ j k, k ≠ i → c ≤ K j k) :
    (D : ℝ) * ((D : ℝ) - 1) * c + (D : ℝ) * b ≤ ∑ j, ∑ k, K j k := by
  classical
  calc
    (D : ℝ) * ((D : ℝ) - 1) * c + (D : ℝ) * b =
        ∑ _j : Fin D, ∑ k : Fin D, if k = i then b else c := by
      simp_rw [sum_one_exception]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ ∑ j, ∑ k, K j k := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      by_cases h : k = i
      · subst k
        simpa using hnested j
      · simpa only [ite_eq_right h] using hsep j k h

private theorem normalize_pair_total (hD : 0 < D) (b c : ℝ) :
    ((D : ℝ)⁻¹)^2 * ((D : ℝ) * ((D : ℝ) - 1) * c + (D : ℝ) * b) =
      (1 - (D : ℝ)⁻¹) * c + (D : ℝ)⁻¹ * b := by
  have hd : (D : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hD)
  field_simp [hd]

variable {G : Type uG} {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The literal finite average of the real inner product. -/
def corr (A : Finset G) (x y : G → E) : ℝ :=
  realAvg A (fun g => ⟪x g, y g⟫_ℝ)

theorem corr_comm (A : Finset G) (x y : G → E) : corr A x y = corr A y x := by
  unfold corr
  apply realAvg_congr
  intro g _
  exact real_inner_comm (y g) (x g)

theorem unit_inner_abs_le (x y : E) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |⟪x, y⟫_ℝ| ≤ 1 := by
  calc
    |⟪x, y⟫_ℝ| ≤ ‖x‖ * ‖y‖ := abs_real_inner_le_norm x y
    _ ≤ 1 * 1 := mul_le_mul hx hy (norm_nonneg y) zero_le_one
    _ = 1 := by ring

theorem corr_abs_le_one (A : Finset G) (hA : A.Nonempty) (x y : G → E)
    (hx : ∀ g ∈ A, ‖x g‖ ≤ 1) (hy : ∀ g ∈ A, ‖y g‖ ≤ 1) :
    |corr A x y| ≤ 1 := by
  unfold corr
  apply abs_le.mpr
  constructor
  · apply const_le_realAvg A hA
    intro g hg
    exact (abs_le.mp (unit_inner_abs_le (x g) (y g) (hx g hg) (hy g hg))).1
  · apply realAvg_le_const A hA
    intro g hg
    exact (abs_le.mp (unit_inner_abs_le (x g) (y g) (hx g hg) (hy g hg))).2

theorem realAvg_norm_finMean_sq (A : Finset G) (x : G → Fin D → E) :
    realAvg A (fun g => ‖finMean (x g)‖^2) =
      ((D : ℝ)⁻¹)^2 * ∑ j, ∑ k, corr A (fun g => x g j) (fun g => x g k) := by
  simp only [norm_finMean_sq, realAvg_const_mul, realAvg_sum_univ, corr]

theorem corr_finMean (A : Finset G) (x y : G → Fin D → E) :
    corr A (fun g => finMean (x g)) (fun g => finMean (y g)) =
      ((D : ℝ)⁻¹)^2 * ∑ j, ∑ k, corr A (fun g => x g j) (fun g => y g k) := by
  simp only [corr, inner_finMean, pow_two, realAvg_const_mul, realAvg_sum_univ]

theorem realAvg_norm_sub_sq (A : Finset G) (x y : G → E) :
    realAvg A (fun g => ‖x g - y g‖^2) =
      realAvg A (fun g => ‖x g‖^2) - 2 * corr A x y +
        realAvg A (fun g => ‖y g‖^2) := by
  simp only [norm_sub_sq_real, realAvg_add, realAvg_sub, realAvg_const_mul, corr]

/-- Parent or sibling averages: the same exact diagonal count applies to both. -/
theorem realAvg_norm_finMean_sq_le (A : Finset G) (hA : A.Nonempty)
    (hD : 0 < D) (x : G → Fin D → E) (c : ℝ)
    (hx : ∀ g ∈ A, ∀ j, ‖x g j‖ ≤ 1)
    (hsep : ∀ j k, j ≠ k → corr A (fun g => x g j) (fun g => x g k) ≤ c) :
    realAvg A (fun g => ‖finMean (x g)‖^2) ≤
      (1 - (D : ℝ)⁻¹) * c + (D : ℝ)⁻¹ := by
  rw [realAvg_norm_finMean_sq]
  have hdiag (j : Fin D) : corr A (fun g => x g j) (fun g => x g j) ≤ 1 :=
    (abs_le.mp (corr_abs_le_one A hA _ _
      (fun g hg => hx g hg j) (fun g hg => hx g hg j))).2
  calc
    ((D : ℝ)⁻¹)^2 * ∑ j, ∑ k, corr A (fun g => x g j) (fun g => x g k) ≤
        ((D : ℝ)⁻¹)^2 * ((D : ℝ) * ((D : ℝ) - 1) * c + (D : ℝ) * 1) :=
      mul_le_mul_of_nonneg_left (sum_matrix_le _ 1 c hdiag hsep) (sq_nonneg _)
    _ = (1 - (D : ℝ)⁻¹) * c + (D : ℝ)⁻¹ := by
      simpa only [mul_one] using normalize_pair_total hD 1 c

/-- Only the designated parent column is uncontrolled in a mixed sum. -/
theorem corr_finMean_ge (A : Finset G) (hA : A.Nonempty) (hD : 0 < D)
    (i : Fin D) (z x : G → Fin D → E) (c : ℝ)
    (hz : ∀ g ∈ A, ∀ j, ‖z g j‖ ≤ 1)
    (hx : ∀ g ∈ A, ∀ k, ‖x g k‖ ≤ 1)
    (hsep : ∀ j k, k ≠ i → c ≤ corr A (fun g => z g j) (fun g => x g k)) :
    (1 - (D : ℝ)⁻¹) * c - (D : ℝ)⁻¹ ≤
      corr A (fun g => finMean (z g)) (fun g => finMean (x g)) := by
  have hnested (j : Fin D) : -1 ≤ corr A (fun g => z g j) (fun g => x g i) :=
    (abs_le.mp (corr_abs_le_one A hA _ _
      (fun g hg => hz g hg j) (fun g hg => hx g hg i))).1
  calc
    (1 - (D : ℝ)⁻¹) * c - (D : ℝ)⁻¹ =
        ((D : ℝ)⁻¹)^2 * ((D : ℝ) * ((D : ℝ) - 1) * c + (D : ℝ) * (-1)) := by
      rw [normalize_pair_total hD]
      ring
    _ ≤ ((D : ℝ)⁻¹)^2 * ∑ j, ∑ k, corr A (fun g => z g j) (fun g => x g k) :=
      mul_le_mul_of_nonneg_left (sum_fixed_column_ge i _ (-1) c hnested hsep)
        (sq_nonneg _)
    _ = corr A (fun g => finMean (z g)) (fun g => finMean (x g)) :=
      (corr_finMean A z x).symm

/-- The finite Hilbert variance bound with exact cancellation of signed alpha. -/
theorem finite_variance_bound (A : Finset G) (hA : A.Nonempty) (hD : 0 < D)
    (x : G → Fin D → E) (y : G → Fin D → Fin D → E) (α η : ℝ)
    (hx : ∀ g ∈ A, ∀ k, ‖x g k‖ ≤ 1)
    (hy : ∀ g ∈ A, ∀ i j, ‖y g i j‖ ≤ 1)
    (hparent : ∀ j k, j ≠ k →
      |corr A (fun g => x g j) (fun g => x g k) - α| ≤ η)
    (hchild : ∀ i j k, j ≠ k →
      |corr A (fun g => y g i j) (fun g => y g i k) - α| ≤ η)
    (hmixed : ∀ i j k, k ≠ i →
      |corr A (fun g => y g i j) (fun g => x g k) - α| ≤ η) :
    ∀ i, realAvg A (fun g => ‖finMean (y g i) - finMean (x g)‖^2) ≤
      4 / (D : ℝ) + 4 * (1 - 1 / (D : ℝ)) * η := by
  intro i
  have hp := realAvg_norm_finMean_sq_le A hA hD x (α + η) hx (by
    intro j k hjk
    have h := (abs_le.mp (hparent j k hjk)).2
    linarith)
  have hq := realAvg_norm_finMean_sq_le A hA hD (fun g => y g i) (α + η)
    (fun g hg => hy g hg i) (by
      intro j k hjk
      have h := (abs_le.mp (hchild i j k hjk)).2
      linarith)
  have hm := corr_finMean_ge A hA hD i (fun g => y g i) x (α - η)
    (fun g hg => hy g hg i) hx (by
      intro j k hki
      have h := (abs_le.mp (hmixed i j k hki)).1
      linarith)
  rw [realAvg_norm_sub_sq]
  calc
    realAvg A (fun g => ‖finMean (y g i)‖^2) -
        2 * corr A (fun g => finMean (y g i)) (fun g => finMean (x g)) +
        realAvg A (fun g => ‖finMean (x g)‖^2) ≤
        ((1 - (D : ℝ)⁻¹) * (α + η) + (D : ℝ)⁻¹) -
          2 * ((1 - (D : ℝ)⁻¹) * (α - η) - (D : ℝ)⁻¹) +
          ((1 - (D : ℝ)⁻¹) * (α + η) + (D : ℝ)⁻¹) := by
      linarith only [hp, hq, hm]
    _ = 4 / (D : ℝ) + 4 * (1 - 1 / (D : ℝ)) * η := by
      simp only [div_eq_mul_inv, one_mul]
      ring

end ThompsonNonamenability

end

end OAI
