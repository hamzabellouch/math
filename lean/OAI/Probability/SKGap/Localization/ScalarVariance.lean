import Mathlib
import OAI.Probability.SKGap.Localization.Invert
import OAI.Probability.SKGap.Localization.JumpWeight

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
namespace SKGapCutoff

noncomputable def scalarVariance (y : ℝ) : ℝ := 1 - Real.tanh y ^ 2

lemma scalarVariance_pos (y : ℝ) : 0 < scalarVariance y :=
  sub_pos.mpr (Real.tanh_sq_lt_one y)

lemma scalarVariance_le_one (y : ℝ) : scalarVariance y ≤ 1 := by
  unfold scalarVariance
  nlinarith [sq_nonneg (Real.tanh y)]

lemma scalarVariance_eq (y : ℝ) : scalarVariance y = 1 / Real.cosh y ^ 2 := by
  have hc := Real.cosh_sq_sub_sinh_sq y
  unfold scalarVariance
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  nlinarith

lemma tanh_hasDerivAt (y : ℝ) : HasDerivAt Real.tanh (scalarVariance y) y := by
  have h := (Real.hasDerivAt_sinh y).div (Real.hasDerivAt_cosh y) (Real.cosh_pos y).ne'
  convert! h using 1
  · ext z; exact Real.tanh_eq_sinh_div_cosh z
  · rw [scalarVariance_eq]
    congr 1
    nlinarith [Real.cosh_sq_sub_sinh_sq y]

lemma tanh_lipschitz (x y : ℝ) : |Real.tanh y - Real.tanh x| ≤ |y-x| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ (Set.univ : Set ℝ)) => (tanh_hasDerivAt z).hasDerivWithinAt)
    (fun z _ => (show ‖scalarVariance z‖ ≤ 1 by
      rw [Real.norm_eq_abs, abs_of_pos (scalarVariance_pos z)]
      exact scalarVariance_le_one z)) convex_univ (Set.mem_univ x) (Set.mem_univ y)
  simpa only [one_mul, Real.norm_eq_abs] using h

lemma scalarVariance_lipschitz (x y : ℝ) : |scalarVariance y - scalarVariance x| ≤ 2*|y-x| := by
  have h1 := tanh_lipschitz x y
  have h2 : |Real.tanh y + Real.tanh x| ≤ 2 :=
    (abs_add_le _ _).trans (by linarith [Real.abs_tanh_lt_one x, Real.abs_tanh_lt_one y])
  have he : scalarVariance y - scalarVariance x =
      -(Real.tanh y - Real.tanh x) * (Real.tanh y + Real.tanh x) := by
    unfold scalarVariance
    ring
  rw [he, abs_mul, abs_neg]
  nlinarith [mul_le_mul h1 h2 (abs_nonneg _) (abs_nonneg _)]

lemma tanh_linear_remainder (x y : ℝ) :
    |Real.tanh y - Real.tanh x - scalarVariance x * (y-x)| ≤ 2 * |y-x| ^ 2 := by
  let f (z : ℝ) := Real.tanh z - Real.tanh x - scalarVariance x * (z-x)
  have hd (z : ℝ) : HasDerivAt f (scalarVariance z - scalarVariance x) z := by
    convert! ((tanh_hasDerivAt z).sub_const (Real.tanh x)).sub
      (((hasDerivAt_id z).sub_const x).const_mul (scalarVariance x)) using 1
    simp only [mul_one]
  have hb (z : ℝ) (hz : z ∈ segment ℝ x y) : ‖scalarVariance z - scalarVariance x‖ ≤
      2 * |y-x| := by
    have hh : |z-x| ≤ |y-x| := by simpa only [Real.norm_eq_abs] using norm_sub_le_of_mem_segment hz
    simpa only [Real.norm_eq_abs] using (scalarVariance_lipschitz x z).trans
      (mul_le_mul_of_nonneg_left hh (by norm_num))
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ segment ℝ x y) => (hd z).hasDerivWithinAt) hb
    (convex_segment x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [f, sub_self, mul_zero, sub_zero, Real.norm_eq_abs, pow_two, mul_assoc] using h

lemma cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

lemma cosh_shift_le (x y : ℝ) : Real.cosh y ≤ Real.exp |y-x| * Real.cosh x := by
  rw [Real.cosh_eq, Real.cosh_eq]
  have h1 : Real.exp y ≤ Real.exp |y-x| * Real.exp x := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [le_abs_self (y-x)]
  have h2 : Real.exp (-y) ≤ Real.exp |y-x| * Real.exp (-x) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [neg_le_abs (y-x)]
  nlinarith

lemma sinh_abs_le (d : ℝ) : |Real.sinh d| ≤ |d| * Real.exp |d| := by
  have hb (z : ℝ) (hz : z ∈ segment ℝ 0 d) : ‖Real.cosh z‖ ≤ Real.exp |d| := by
    have hh : |z| ≤ |d| := by
      simpa only [sub_zero, Real.norm_eq_abs] using norm_sub_le_of_mem_segment hz
    rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos z)]
    exact (cosh_le_exp_abs z).trans (Real.exp_le_exp.mpr hh)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ segment ℝ 0 d) => (Real.hasDerivAt_sinh z).hasDerivWithinAt) hb
    (convex_segment 0 d) (left_mem_segment ℝ 0 d) (right_mem_segment ℝ 0 d)
  simpa only [Real.sinh_zero, sub_zero, Real.norm_eq_abs, mul_comm] using h

lemma tanh_difference_eq (x y : ℝ) : Real.tanh y - Real.tanh x =
    Real.sinh (y-x) / (Real.cosh y * Real.cosh x) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Real.sinh_sub]
  field_simp

lemma tanh_difference_variance_le (x y : ℝ) :
    |Real.tanh y - Real.tanh x| ≤ |y-x| * Real.exp (2*|y-x|) * scalarVariance y := by
  have hc := cosh_shift_le x y
  have hs := sinh_abs_le (y-x)
  have hp := mul_le_mul hs hc (Real.cosh_pos y).le
    (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
  rw [scalarVariance_eq, tanh_difference_eq, abs_div,
    abs_of_pos (mul_pos (Real.cosh_pos y) (Real.cosh_pos x))]
  rw [mul_one_div, div_le_div_iff₀ (mul_pos (Real.cosh_pos y) (Real.cosh_pos x))
    (sq_pos_of_pos (Real.cosh_pos y))]
  have he : Real.exp (2*|y-x|) = Real.exp |y-x| * Real.exp |y-x| := by
    rw [two_mul, Real.exp_add]
  rw [he]
  have hh := mul_le_mul_of_nonneg_right hp (Real.cosh_pos y).le
  nlinarith

lemma field_flip_general {n : ℕ} (J : Interaction n) (x : Spin n) (i j : Fin n) :
    field J (flip x i) j = field J x j - 2 * J j i * spin x i := by
  simp only [field, spin_flip, mul_sub, Finset.sum_sub_distrib]
  simp [mul_ite]
  ring

lemma halfDiff_as_flip {n : ℕ} (f : Observables n) (x : Spin n) (i : Fin n) :
    halfDiff i f x = spin x i * (f x - f (flip x i)) / 2 := by
  have hx := replace_self x i
  cases hi : x i <;> simp only [hi] at hx
  · simp only [spin, hi, Bool.false_eq_true, ↓reduceIte, flip, Bool.not_false, halfDiff]
    rw [hx]; ring
  · simp only [spin, hi, ↓reduceIte, flip, Bool.not_true, halfDiff]
    rw [hx]; ring

lemma abs_spin_eq_one {n : ℕ} (x : Spin n) (i : Fin n) : |spin x i| = 1 := by
  cases hi : x i <;> simp [spin, hi]

lemma abs_field_change {n : ℕ} (J : Interaction n) (x : Spin n) (i j : Fin n) :
    |field J x j - field J (flip x i) j| = 2 * |J j i| := by
  rw [field_flip_general]
  ring_nf
  simp [abs_mul, abs_spin_eq_one, mul_comm]

lemma influence_error_le {n : ℕ} (J : Interaction n) (x : Spin n) (i j : Fin n) :
    |influence J x i j - J j i * siteVariance J x j| ≤ 4 * J j i ^ 2 := by

  have hr := tanh_linear_remainder (field J x j) (field J (flip x i) j)
  have he : influence J x i j - J j i * siteVariance J x j =
      -(spin x i / 2) * (Real.tanh (field J (flip x i) j) - Real.tanh (field J x j) -
        scalarVariance (field J x j) * (field J (flip x i) j - field J x j)) := by
    simp only [influence, halfDiff_as_flip, mean, siteVariance, scalarVariance, field_flip_general]
    linear_combination J j i * (1 - Real.tanh (field J x j) ^ 2) * (spin_sq x i)
  rw [he, abs_mul, abs_neg, abs_div, abs_spin_eq_one]
  norm_num only [abs_of_pos (show (0:ℝ) < 2 by norm_num)]
  have ha : |field J (flip x i) j - field J x j| = 2 * |J j i| := by
    rw [abs_sub_comm, abs_field_change]
  rw [ha] at hr
  nlinarith [sq_abs (J j i)]

lemma influence_variance_le {n : ℕ} (J : Interaction n) (x : Spin n) (i j : Fin n) :
    |influence J x i j| ≤ |J j i| * Real.exp (4*|J j i|) * siteVariance J x j := by
  have h := tanh_difference_variance_le (field J (flip x i) j) (field J x j)
  rw [abs_field_change] at h
  rw [influence, halfDiff_as_flip, abs_div, abs_mul, abs_spin_eq_one, one_mul]
  norm_num only [abs_of_pos (show (0:ℝ) < 2 by norm_num)]
  change |Real.tanh (field J x j) - Real.tanh (field J (flip x i) j)| / 2 ≤ _
  change _ ≤ |J j i| * Real.exp (4*|J j i|) * scalarVariance (field J x j)
  have he : 2 * (2 * |J j i|) = 4*|J j i| := by ring
  rw [he] at h
  linarith

lemma siteVariance_sq_le_jumpWeight {n : ℕ} (J : Interaction n) (x : Spin n) (j : Fin n) :
    siteVariance J x j ^ 2 ≤ 2 * jumpWeight J x j := by
  have hv := siteVariance_pos J x j
  have hv1 := siteVariance_le_one J x j
  have hw := jumpWeight_pos J x j
  have hm : mean J x j * spin x j ≤ 1 := by
    have ha : |mean J x j * spin x j| < 1 := by
      simpa only [mean, abs_mul, abs_spin_eq_one, mul_one] using Real.abs_tanh_lt_one (field J x j)
    exact (le_abs_self _).trans ha.le
  have he : siteVariance J x j = jumpWeight J x j * (1 + mean J x j * spin x j) := by
    unfold siteVariance jumpWeight
    have hs := spin_sq x j
    nlinarith
  have h2 := mul_le_mul_of_nonneg_left (show 1 + mean J x j * spin x j ≤ 2 by linarith) hw.le
  rw [← he] at h2
  nlinarith

lemma influence_weighted_entry_le {n : ℕ} (J : Interaction n) (x : Spin n) (i j : Fin n)
    (c : ℝ) (hc : |J j i| ≤ c) :
    influence J x i j ^ 2 / jumpWeight J x j ≤ 2 * Real.exp (8*c) * J j i ^ 2 := by
  have h := influence_variance_le J x i j
  have h' : |influence J x i j| ≤ |J j i| * Real.exp (4*c) * siteVariance J x j := by
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (siteVariance_pos J x j).le
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hc (by norm_num))
  have hs := sq_le_sq₀ (abs_nonneg (influence J x i j))
    (mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (siteVariance_pos J x j).le) |>.mpr h'
  simp only [sq_abs, mul_pow] at hs
  have hv := mul_le_mul_of_nonneg_left (siteVariance_sq_le_jumpWeight J x j)
    (mul_nonneg (sq_nonneg (J j i)) (sq_nonneg (Real.exp (4*c))))
  have he : Real.exp (4*c)^2 = Real.exp (8*c) := by rw [← Real.exp_nat_mul]; congr 1; ring
  rw [he] at hs hv
  apply (div_le_iff₀ (jumpWeight_pos J x j)).mpr
  nlinarith

lemma influence_weighted_row_le {n : ℕ} (J : Interaction n) (x : Spin n)
    (c M : ℝ) (hc : ∀ i j, |J i j| ≤ c) (hM : ∀ i, ∑ j, J j i ^ 2 ≤ M) (i : Fin n) :
    ∑ j, influence J x i j ^ 2 / jumpWeight J x j ≤ 2 * Real.exp (8*c) * M := by
  calc
    _ ≤ ∑ j, 2 * Real.exp (8*c) * J j i ^ 2 :=
      Finset.sum_le_sum (fun j _ => influence_weighted_entry_le J x i j c (hc j i))
    _ = 2 * Real.exp (8*c) * ∑ j, J j i ^ 2 := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hM i) (by positivity)

lemma influence_error_quadratic_le {n : ℕ} (J : Interaction n) (hJ : ∀ i j, J i j = J j i)
    (x : Spin n) (u : Fin n → ℝ) (M : ℝ) (hM : ∀ i, ∑ j, J j i ^ 2 ≤ M) :
    |∑ i, ∑ j, u i * (influence J x i j - J j i * siteVariance J x j) * u j| ≤
      4 * M * ∑ i, u i ^ 2 := by
  have he (i j : Fin n) :
      |u i * (influence J x i j - J j i * siteVariance J x j) * u j| ≤
      2 * J j i ^ 2 * (u i ^ 2 + u j ^ 2) := by
    rw [abs_mul, abs_mul]
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (influence_error_le J x i j) (abs_nonneg (u i)))
      (abs_nonneg (u j))
    have hs : 2 * |u i| * |u j| ≤ u i ^ 2 + u j ^ 2 := by
      nlinarith [sq_nonneg (|u i|-|u j|), sq_abs (u i), sq_abs (u j)]
    have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * J j i ^ 2 by positivity)
    nlinarith
  have ha : |∑ i, ∑ j, u i * (influence J x i j - J j i * siteVariance J x j) * u j| ≤
      ∑ i, ∑ j, 2 * J j i ^ 2 * (u i ^ 2 + u j ^ 2) := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ =>
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => he i j))))
  have hr : (∑ i, ∑ j, J j i ^ 2 * u i ^ 2) ≤ M * ∑ i, u i ^ 2 := by
    calc
      _ = ∑ i, (∑ j, J j i ^ 2) * u i ^ 2 := by simp_rw [Finset.sum_mul]
      _ ≤ ∑ i, M * u i ^ 2 := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_right (hM i) (sq_nonneg _))
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hc : (∑ i, ∑ j, J j i ^ 2 * u j ^ 2) ≤ M * ∑ i, u i ^ 2 := by
    rw [Finset.sum_comm]
    simpa only [hJ] using hr
  have hs : (∑ i, ∑ j, 2 * J j i ^ 2 * (u i ^ 2 + u j ^ 2)) =
      2 * (∑ i, ∑ j, J j i ^ 2 * u i ^ 2) +
      2 * (∑ i, ∑ j, J j i ^ 2 * u j ^ 2) := by
    simp_rw [mul_add, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hs] at ha
  linarith

lemma influence_quadratic_le {n : ℕ} (J : Interaction n) (hJ : ∀ i j, J i j = J j i)
    (x : Spin n) (u : Fin n → ℝ) (B M : ℝ) (hB : 0 ≤ B)
    (hJB : ∀ a b : Fin n → ℝ, |∑ i, ∑ j, a i * J j i * b j| ≤
      B / 2 * ((∑ i, a i ^ 2) + ∑ j, b j ^ 2))
    (hM : ∀ i, ∑ j, J j i ^ 2 ≤ M) :
    ∑ i, u i * (∑ j, influence J x i j * u j) ≤ (B + 4*M) * ∑ i, u i ^ 2 := by
  have hv : (∑ j, (siteVariance J x j * u j)^2) ≤ ∑ j, u j ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    have hp := siteVariance_pos J x j
    have h1 := siteVariance_le_one J x j
    have hv : siteVariance J x j ^ 2 ≤ 1 := by nlinarith
    simpa only [mul_pow, one_mul] using mul_le_mul_of_nonneg_right hv (sq_nonneg (u j))
  have hb := hJB u (fun j => siteVariance J x j * u j)
  have hb' : (∑ i, ∑ j, u i * J j i * (siteVariance J x j * u j)) ≤ B * ∑ i, u i ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hv (show 0 ≤ B/2 by positivity)
    linarith [le_abs_self (∑ i, ∑ j, u i * J j i * (siteVariance J x j * u j))]
  have he := influence_error_quadratic_le J hJ x u M hM
  have hs : (∑ i, u i * (∑ j, influence J x i j * u j)) =
      (∑ i, ∑ j, u i * J j i * (siteVariance J x j * u j)) +
      (∑ i, ∑ j, u i * (influence J x i j - J j i * siteVariance J x j) * u j) := by
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  have hh := le_abs_self (∑ i, ∑ j, u i * (influence J x i j - J j i * siteVariance J x j) * u j)
  nlinarith

end SKGapCutoff

open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set

end

end OAI
