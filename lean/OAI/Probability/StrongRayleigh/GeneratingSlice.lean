import OAI.Probability.StrongRayleigh.TiltScaling
import OAI.Probability.StrongRayleigh.TiltPartition

namespace OAI

universe u_1

noncomputable section

open MeasureTheory Polynomial
open scoped BigOperators ENNReal

namespace Problem336AdditiveD139
namespace GeneratingSlice

variable {F : Type u_1} [Fintype F] [DecidableEq F]

def countExcept (i : F) (x : F → Bool) : ℕ := by
  classical
  exact ∑ j ∈ Finset.univ.erase i, if x j = true then 1 else 0

def weight (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (x : F → Bool) : ℝ :=
  Real.exp (∑ j : F, h j * boolReal (x j)) * ((μ : Measure (F → Bool)) {x}).toReal

def slice (w : (F → Bool) → ℝ) (i : F) (b : Bool) : ℝ[X] := by
  classical
  exact ∑ x : F → Bool, if x i = b then C (w x) * X ^ countExcept i x else 0

omit [DecidableEq F] in
lemma weight_nonneg (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (x : F → Bool) :
    0 ≤ weight μ h x := mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg

lemma countExcept_cast (i : F) (x : F → Bool) :
    (countExcept i x : ℝ) = ∑ j ∈ Finset.univ.erase i, boolReal (x j) := by
  classical
  simp only [countExcept, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  cases x j <;> simp [boolReal]

lemma countExcept_add_bit (i : F) (x : F → Bool) :
    (countExcept i x : ℝ) + boolReal (x i) = ∑ j : F, boolReal (x j) := by
  classical
  rw [countExcept_cast]
  exact Finset.sum_erase_add _ _ (Finset.mem_univ i)

lemma monomial_except (i : F) (x : F → Bool) (z : ℂ) :
    (∏ j ∈ Finset.univ.erase i, if x j = true then z else 1) = z ^ countExcept i x := by
  classical
  unfold countExcept
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro j hj
  cases x j <;> simp

lemma monomial_slice (i : F) (x : F → Bool) (z s : ℂ) :
    (∏ j : F, if x j = true then (if j = i then s else z) else 1) =
      (if x i = true then s else 1) * z ^ countExcept i x := by
  classical
  have hs := Finset.prod_erase_mul Finset.univ
    (fun j => if x j = true then (if j = i then s else z) else 1) (Finset.mem_univ i)
  rw [← hs]
  have he : (∏ j ∈ Finset.univ.erase i,
      if x j = true then (if j = i then s else z) else 1) =
      ∏ j ∈ Finset.univ.erase i, if x j = true then z else 1 := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [(Finset.mem_erase.mp hj).1]
  rw [he, monomial_except]
  simp [mul_comm]

lemma slice_eval (w : (F → Bool) → ℝ) (i : F) (b : Bool) (t : ℝ) :
    (slice w i b).eval t = ∑ x : F → Bool,
      if x i = b then w x * t ^ countExcept i x else 0 := by
  classical
  simp only [slice, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp

lemma slice_eval_one (w : (F → Bool) → ℝ) (i : F) (b : Bool) :
    (slice w i b).eval 1 = ∑ x : F → Bool, if x i = b then w x else 0 := by
  simp [slice_eval]

lemma slice_aeval (w : (F → Bool) → ℝ) (i : F) (b : Bool) (z : ℂ) :
    aeval z (slice w i b) = ∑ x : F → Bool,
      if x i = b then (w x : ℂ) * z ^ countExcept i x else 0 := by
  classical
  simp only [slice, map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp

lemma slice_derivative_eval_one (w : (F → Bool) → ℝ) (i : F) (b : Bool) :
    (slice w i b).derivative.eval 1 = ∑ x : F → Bool,
      if x i = b then w x * (countExcept i x : ℝ) else 0 := by
  classical
  simp only [slice, Polynomial.derivative_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp [Polynomial.derivative_mul, Polynomial.derivative_X_pow]

lemma slice_coeff_nonneg (w : (F → Bool) → ℝ) (hw : ∀ x, 0 ≤ w x)
    (i : F) (b : Bool) (n : ℕ) : 0 ≤ (slice w i b).coeff n := by
  classical
  simp only [slice, Polynomial.finsetSum_coeff]
  apply Finset.sum_nonneg
  intro x hx
  split_ifs
  · simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split_ifs <;> simp [hw]
  · simp

lemma slice_eval_one_add (w : (F → Bool) → ℝ) (i : F) :
    (slice w i false).eval 1 + (slice w i true).eval 1 = ∑ x : F → Bool, w x := by
  classical
  rw [slice_eval_one, slice_eval_one, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  cases x i <;> simp

lemma slice_generating_identity (μ : ProbabilityMeasure (F → Bool))
    (h : F → ℝ) (i : F) (z s : ℂ) :
    aeval z (slice (weight μ h) i false) + s * aeval z (slice (weight μ h) i true) =
      finiteGeneratingValue μ (fun j => (Real.exp (h j) : ℂ) * (if j = i then s else z)) := by
  classical
  rw [slice_aeval, slice_aeval, Finset.mul_sum, ← Finset.sum_add_distrib]
  unfold finiteGeneratingValue
  apply Finset.sum_congr (by ext x; simp)
  intro x hx
  rw [generating_monomial_rescale, monomial_slice]
  cases x i <;> simp [weight, mul_comm, mul_assoc]

lemma slice_stable (μ : ProbabilityMeasure (F → Bool)) (hμ : StronglyRayleighFinite μ)
    (h : F → ℝ) (i : F) (z s : ℂ) (hz : 0 < z.im) (hs : 0 < s.im) :
    aeval z (slice (weight μ h) i false) + s * aeval z (slice (weight μ h) i true) ≠ 0 := by
  rw [slice_generating_identity]
  apply hμ
  intro j
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  apply mul_pos (Real.exp_pos _)
  split_ifs <;> assumption

lemma slice_true_eval_one (w : (F → Bool) → ℝ) (i : F) :
    (slice w i true).eval 1 = ∑ x : F → Bool, w x * boolReal (x i) := by
  rw [slice_eval_one]
  apply Finset.sum_congr rfl
  intro x hx
  cases x i <;> simp [boolReal]

lemma slice_derivative_add (w : (F → Bool) → ℝ) (i : F) :
    (slice w i false).derivative.eval 1 + (slice w i true).derivative.eval 1 =
      ∑ x : F → Bool, w x * (countExcept i x : ℝ) := by
  rw [slice_derivative_eval_one, slice_derivative_eval_one, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  cases x i <;> simp

lemma slice_true_derivative_add (w : (F → Bool) → ℝ) (i : F) :
    (slice w i true).derivative.eval 1 + (slice w i true).eval 1 =
      ∑ x : F → Bool, w x * boolReal (x i) * (∑ j : F, boolReal (x j)) := by
  rw [slice_derivative_eval_one, slice_eval_one, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← countExcept_add_bit i x]
  cases x i <;> simp [boolReal]
  ring

lemma slice_total_derivative_add (w : (F → Bool) → ℝ) (i : F) :
    (slice w i false).derivative.eval 1 + (slice w i true).derivative.eval 1 +
        (slice w i true).eval 1 =
      ∑ x : F → Bool, w x * (∑ j : F, boolReal (x j)) := by
  rw [slice_derivative_add, slice_true_eval_one, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← countExcept_add_bit i x]
  ring

lemma slice_sum_eq_partition (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i : F) :
    (slice (weight μ h) i false).eval 1 + (slice (weight μ h) i true).eval 1 =
      tiltPartition μ h := by
  rw [slice_eval_one_add]
  unfold tiltPartition weight
  apply Finset.sum_congr (by ext; simp)
  intros
  rfl

lemma tiltMean_eq_slice (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i : F) :
    tiltMean μ h i = (slice (weight μ h) i true).eval 1 / tiltPartition μ h := by
  rw [slice_true_eval_one]
  unfold tiltMean weight
  congr 1
  apply Finset.sum_congr (by ext; simp)
  intros
  rfl

lemma sum_tiltMean_eq_slice (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i : F) :
    (∑ j : F, tiltMean μ h j) =
      ((slice (weight μ h) i false).derivative.eval 1 +
        (slice (weight μ h) i true).derivative.eval 1 +
        (slice (weight μ h) i true).eval 1) / tiltPartition μ h := by
  rw [slice_total_derivative_add]
  unfold tiltMean
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr (by ext; simp)
  intro x hx
  simp [weight, Finset.mul_sum]

lemma sum_tiltSecondMoment_eq_slice (μ : ProbabilityMeasure (F → Bool))
    (h : F → ℝ) (i : F) :
    (∑ j : F, tiltSecondMoment μ h i j) =
      ((slice (weight μ h) i true).derivative.eval 1 +
        (slice (weight μ h) i true).eval 1) / tiltPartition μ h := by
  rw [slice_true_derivative_add]
  unfold tiltSecondMoment
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr (by ext; simp)
  intro x hx
  simp [weight, Finset.mul_sum]

theorem covariance_row_eq_slice (μ : ProbabilityMeasure (F → Bool))
    (h : F → ℝ) (i : F) :
    (∑ j : F, tiltCovariance μ h i j) =
      ((slice (weight μ h) i false).eval 1 * (slice (weight μ h) i true).eval 1 +
        (slice (weight μ h) i false).eval 1 * (slice (weight μ h) i true).derivative.eval 1 -
        (slice (weight μ h) i true).eval 1 * (slice (weight μ h) i false).derivative.eval 1) /
      (tiltPartition μ h) ^ 2 := by
  simp only [tiltCovariance, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_tiltSecondMoment_eq_slice, sum_tiltMean_eq_slice μ h i, tiltMean_eq_slice]
  have hZ := tiltPartition_ne_zero μ h
  have heq := slice_sum_eq_partition μ h i
  field_simp
  rw [← heq]
  ring

theorem covariance_row_nonneg_of_slice_bound (μ : ProbabilityMeasure (F → Bool))
    (h : F → ℝ) (i : F)
    (hbound : (slice (weight μ h) i true).eval 1 *
        (slice (weight μ h) i false).derivative.eval 1 -
        (slice (weight μ h) i false).eval 1 * (slice (weight μ h) i true).derivative.eval 1 ≤
        (slice (weight μ h) i false).eval 1 * (slice (weight μ h) i true).eval 1) :
    0 ≤ ∑ j : F, tiltCovariance μ h i j := by
  rw [covariance_row_eq_slice]
  exact div_nonneg (by linarith) (sq_nonneg _)

end GeneratingSlice
end Problem336AdditiveD139

end

end OAI
