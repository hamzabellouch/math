import OAI.Geometry.RCD.Metric.LowerCurvatureVolume

namespace OAI

/-! # Uniform nearby-ball volume ratios at bounded rescaled curvature

Only the existing CD condition is used. Nonnegative curvature uses the
Euclidean ratio, and negative curvature uses the exponential distortion
bound. The resulting constant is chosen before the center and radius.
-/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The exact polynomial lower bound behind the scale-uniform volume factor. -/
theorem NoncollapsedRCD.rescaled_ball_volume_lower {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {a δ : ℝ}
    (ha : 0 ≤ a) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (p : X) (R : ℝ) (hR : 0 < R) (hcurv : -a ≤ K*R^2)
    (y : X) (hy : dist y p ≤ R) :
    (δ/(2*Real.exp (4*Real.sqrt a)))^n*(hausdorff n X).real (ball p R) ≤
      (hausdorff n X).real (ball y (δ*R)) := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let E := Real.exp (4 * Real.sqrt a)
  have hE : 0 < E := Real.exp_pos _
  have hsub : ball p R ⊆ ball y (2 * R) := by
    apply Metric.ball_subset_ball'
    rw [dist_comm]
    linarith only [hy]
  have hr : 0 < δ * R := mul_pos hδ hR
  have hrR : δ * R ≤ 2 * R := by nlinarith only [hδ1, hR]
  have hratio : δ * R / (2 * R) = δ / 2 := by field_simp
  have hsmall : (ENNReal.ofReal (δ / (2 * E))) ^ n *
      (hausdorff n X) (ball p R) ≤ (hausdorff n X) (ball y (δ * R)) := by
    by_cases hK : 0 ≤ K
    · have hcoef : δ / (2 * E) ≤ δ * R / (2 * R) := by
        rw [hratio]
        have hE1 : 1 ≤ E := Real.one_le_exp_iff.mpr (by positivity)
        apply (div_le_iff₀ (by positivity : 0 < 2 * E)).mpr
        nlinarith only [mul_le_mul_of_nonneg_left hE1 hδ.le]
      calc
        _ ≤ (ENNReal.ofReal (δ * R / (2 * R))) ^ n *
            (hausdorff n X) (ball y (2 * R)) :=
          mul_le_mul' (pow_le_pow_left' (ENNReal.ofReal_le_ofReal hcoef) _)
            (measure_mono hsub)
        _ ≤ _ := hX.cd.nonneg_ball_ratio _ K n hX.fullSupport hX.finiteOnBounded
          hn hK y (δ * R) (2 * R) hr hrR
    · have hKneg : K < 0 := lt_of_not_ge hK
      have hNm : 1 ≤ (n : ℝ) - 1 := by
        have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
        linarith only [hnreal]
      have hNm0 : 0 < (n : ℝ) - 1 := zero_lt_one.trans_le hNm
      have hquot : -K / ((n : ℝ) - 1) ≤ -K :=
        div_le_self (neg_nonneg.mpr hKneg.le) hNm
      have hsq : (R * Real.sqrt (-K / ((n : ℝ) - 1))) ^ 2 ≤ a := by
        rw [mul_pow, Real.sq_sqrt (div_nonneg (neg_nonneg.mpr hKneg.le) hNm0.le)]
        have hh := mul_le_mul_of_nonneg_left hquot (sq_nonneg R)
        nlinarith only [hh, hcurv]
      have hsqrt : R * Real.sqrt (-K / ((n : ℝ) - 1)) ≤ Real.sqrt a := by
        nlinarith only [hsq, Real.sq_sqrt ha, Real.sqrt_nonneg a,
          mul_nonneg hR.le (Real.sqrt_nonneg (-K / ((n : ℝ) - 1)))]
      have hExp : Real.exp ((2 * (2 * R)) * Real.sqrt (|K| / ((n : ℝ) - 1))) ≤ E := by
        apply Real.exp_le_exp.mpr
        rw [abs_of_neg hKneg]
        nlinarith only [hsqrt]
      have hcoef : ENNReal.ofReal (δ / (2 * E)) ≤
          distortionFloor K n (2 * (2 * R)) (δ * R / (2 * R)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hratio]
        calc
          δ / (2 * E) = (δ / 2) / E := by ring
          _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hExp
      calc
        _ ≤ distortionFloor K n (2 * (2 * R)) (δ * R / (2 * R)) ^ n *
            (hausdorff n X) (ball y (2 * R)) :=
          mul_le_mul' (pow_le_pow_left' hcoef _) (measure_mono hsub)
        _ ≤ _ := hX.cd.ball_ratio _ K n hX.fullSupport hX.finiteOnBounded
          hn y (δ * R) (2 * R) hr hrR
  have hreal := ENNReal.toReal_mono (hX.finiteOnBounded _ isBounded_ball).ne hsmall
  have hcoef0 : 0 ≤ δ / (2 * E) := (div_pos hδ (by positivity)).le
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hcoef0] at hreal
  exact hreal


theorem NoncollapsedRCD.rescaled_ball_volume_factor {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {a δ : ℝ}
    (ha : 0 ≤ a) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (p : X) (R : ℝ), 0 < R → -a ≤ K * R ^ 2 →
      ∀ y : X, dist y p ≤ R →
        (hausdorff n X).real (ball p R) ≤
          D * (hausdorff n X).real (ball y (δ * R)) := by
  let b := (δ/(2*Real.exp (4*Real.sqrt a)))^n
  have hb : 0 < b := pow_pos (div_pos hδ (by positivity)) _
  refine ⟨max 1 b⁻¹,le_max_left _ _,?_⟩
  intro p R hR hcurv y hy
  have hreal := hX.rescaled_ball_volume_lower hn ha hδ hδ1 p R hR hcurv y hy
  have hh : (hausdorff n X).real (ball p R) ≤
      b⁻¹*(hausdorff n X).real (ball y (δ*R)) := by
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hb).mpr (by simpa only [b,mul_comm] using hreal)
  exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) ENNReal.toReal_nonneg)


end RegularPointCoordinates

end

end OAI
