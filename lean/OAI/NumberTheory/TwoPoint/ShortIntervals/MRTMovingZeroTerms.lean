import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterMovingCenter

namespace OAI

/-! The one-zero de la Vallée Poussin estimate on a shrinking disk.
All constants retain the physical radius and logarithmic growth budget. -/

namespace TwoPointCorrelations

open Complex Finset
open scoped BigOperators Classical

variable {q : ℕ} [NeZero q]

noncomputable def mrtMovingRealPoint (r σ : ℝ) : ℂ :=
  (((σ - 1 - 2 * r) / (3 * r) : ℝ) : ℂ)

lemma mrt_moving_real_point {r : ℝ} (hr : 0 < r) (t σ : ℝ) :
    mrtMovingPoint r t (mrtMovingRealPoint r σ) = (σ : ℂ) + Complex.I * (t : ℂ) := by
  unfold mrtMovingPoint mrtMovingRealPoint
  push_cast
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp [hrC]
  ring

lemma mrt_moving_real_point_norm {r σ : ℝ} (hr : 0 < r)
    (hσ : 1 - r / 4 ≤ σ) (hσ2 : σ ≤ 1 + r) :
    ‖mrtMovingRealPoint r σ‖ ≤ 3 / 4 := by
  rw [mrtMovingRealPoint, Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 3 * r)).mpr
    nlinarith
  · apply (div_le_iff₀ (by positivity : 0 < 3 * r)).mpr
    nlinarith

lemma mrt_moving_zero_physical (χ : DirichletCharacter ℂ q)
    {r t : ℝ} (hr : 0 < r) {ρ : ℂ}
    (hρ : ρ ∈ mrtDiskZeros (mrtMovingLFunction χ r t)) :
    DirichletCharacter.LFunction χ (mrtMovingPoint r t ρ) = 0 := by
  exact (div_eq_zero_iff.mp hρ.2).resolve_right (mrt_moving_point_center_ne_zero χ hr t)

lemma mrt_moving_zero_re (χ : DirichletCharacter ℂ q)
    {r t : ℝ} (hr : 0 < r) (ht : 3 * r < |t|) {ρ : ℂ}
    (hρ : ρ ∈ mrtDiskZeros (mrtMovingLFunction χ r t)) : ρ.re < -(2 / 3 : ℝ) := by
  have hρn : ‖ρ‖ ≤ 7 / 8 := by simpa using hρ.1
  have hn := mrt_moving_point_ne_one hr ht (hρn.trans (by norm_num))
  have hzero := mrt_moving_zero_physical χ hr hρ
  by_contra! hh
  have hσ : 1 ≤ (mrtMovingPoint r t ρ).re := by
    simp only [mrtMovingPoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
    nlinarith
  exact χ.LFunction_ne_zero_of_one_le_re (Or.inr hn) hσ hzero

lemma mrt_moving_zero_term_nonneg (χ : DirichletCharacter ℂ q)
    {r t σ : ℝ} (hr : 0 < r) (ht : 3 * r < |t|) (hσ : 1 < σ)
    {ρ : ℂ} (hρ : ρ ∈ mrtDiskZeros (mrtMovingLFunction χ r t)) :
    0 ≤ (((analyticOrderAt (mrtMovingLFunction χ r t) ρ).toNat : ℂ) /
      (mrtMovingRealPoint r σ - ρ)).re := by
  have hh := mrt_moving_zero_re χ hr ht hρ
  have hd : 0 ≤ (mrtMovingRealPoint r σ - ρ).re := by
    simp only [Complex.sub_re, mrtMovingRealPoint, Complex.ofReal_re]
    have hfrac : -(2 / 3 : ℝ) ≤ (σ - 1 - 2 * r) / (3 * r) := by
      apply (le_div_iff₀ (by positivity : 0 < 3 * r)).mpr
      nlinarith
    linarith
  rw [Complex.div_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hd) (Complex.normSq_nonneg _)

/-- Dropping the nonnegative zero terms gives an upper bound for `-L'/L`. -/
theorem mrt_moving_neg_logderiv (χ : DirichletCharacter ℂ q)
    {r t B σ : ℝ} (hr : 0 < r) (ht : 3 * r < |t|) (hB : 0 < B)
    (hg : ∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
      ‖mrtMovingLFunction χ r t z‖ ≤ Real.exp B)
    (hσ : 1 < σ) (hσ2 : σ ≤ 1 + r) :
    (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (t : ℂ)) /
      DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))).re ≤
        mrtCharacterLogDerivativeConstant * B / (3 * r) := by
  let f := mrtMovingLFunction χ r t
  have hf := mrt_moving_LFunction_analytic χ hr ht
  have h0 := mrt_moving_LFunction_zero χ hr t
  have hz := mrt_moving_real_point_norm hr (by linarith) hσ2
  have hn : DirichletCharacter.LFunction χ (mrtMovingPoint r t (mrtMovingRealPoint r σ)) ≠ 0 := by
    rw [mrt_moving_real_point hr]
    exact χ.LFunction_ne_zero_of_one_le_re (Or.inr (by
      intro he; have hre := congrArg Complex.re he; simp at hre; linarith)) (by simpa using hσ.le)
  have hfn : f (mrtMovingRealPoint r σ) ≠ 0 :=
    div_ne_zero hn (mrt_moving_point_center_ne_zero χ hr t)
  have he := mrt_disk_logderiv f hf h0 hB hg hz hfn
  have hlow := (abs_le.mp ((Complex.abs_re_le_norm _).trans he)).1
  have hs : 0 ≤ ∑ ρ ∈ (mrtDiskZeros_finite f hf h0).toFinset,
      (((analyticOrderAt f ρ).toNat : ℂ) / (mrtMovingRealPoint r σ - ρ)).re := by
    apply sum_nonneg
    intro ρ hρ
    exact mrt_moving_zero_term_nonneg χ hr ht hσ
      ((mrtDiskZeros_finite f hf h0).mem_toFinset.mp hρ)
  rw [Complex.sub_re, Complex.re_sum] at hlow
  rw [mrt_moving_logderiv_eq χ hr ht (hz.trans (by norm_num)) hn,
    mrt_moving_real_point hr] at hlow
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hlow
  simp only [neg_div, Complex.neg_re]
  apply (le_div_iff₀ (by positivity : 0 < 3 * r)).mpr
  nlinarith only [hlow, hs]

end TwoPointCorrelations

end OAI
