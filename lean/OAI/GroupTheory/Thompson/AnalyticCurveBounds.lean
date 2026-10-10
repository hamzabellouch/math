import OAI.GroupTheory.Thompson.AnalyticCurve
import OAI.GroupTheory.Thompson.AnalyticNormalization
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-!
# Quantitative estimates for the actual Hilbert curve

The derivative estimate uses first-derivative product differences on the
oscillating part and the exact straight-tail formula. No second derivative
at a profile junction is assumed.
-/

noncomputable section

namespace ThompsonNonamenability.Analytic

open Set
open scoped NNReal

theorem a_sub_abs_le (s t : ℝ) : |a s - a t| ≤ (1 / 8) * |s - t| := by
  simpa only [Real.dist_eq, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
    a_lipschitz.dist_le_mul s t

theorem aDeriv_sub_abs_le (s t : ℝ) :
    |aDeriv s - aDeriv t| ≤ (1 / 8) * |s - t| := by
  simpa only [Real.dist_eq, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
    aDeriv_lipschitz.dist_le_mul s t

theorem theta_sub_abs_le (s t : ℝ) : |theta s - theta t| ≤ |s - t| := by
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using theta_lipschitz.dist_le_mul s t

theorem thetaDeriv_sub_abs_le (s t : ℝ) :
    |thetaDeriv s - thetaDeriv t| ≤ |s - t| := by
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
    thetaDeriv_lipschitz.dist_le_mul s t

theorem waveDeriv_norm_le_one (z : ℝ) : ‖waveDeriv z‖ ≤ 1 := by
  have := waveDeriv_norm_sq z
  nlinarith [norm_nonneg (waveDeriv z)]

theorem v_sub_norm_le_forward (s t : ℝ) : ‖v s - v t‖ ≤ |s - t| :=
  (wave_sub_norm_le (theta s) (theta t)).trans (theta_sub_abs_le s t)

theorem v_lipschitz : LipschitzWith 1 v := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using
    v_sub_norm_le_forward s t

/-- A product difference estimate with the coefficient difference at the first vector. -/
theorem smul_sub_smul_norm_le (r q : ℝ) (x y : Hilbert) :
    ‖r • x - q • y‖ ≤ |r - q| * ‖x‖ + |q| * ‖x - y‖ := by
  have he : r • x - q • y = (r - q) • x + q • (x - y) := by
    simp only [sub_smul, smul_sub]
    abel
  rw [he]
  simpa only [norm_smul, Real.norm_eq_abs] using
    norm_add_le ((r - q) • x) (q • (x - y))

/-- The second coefficient in the derivative is nonnegative and uniformly bounded. -/
theorem angularCoeff_bounds {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ a t * thetaDeriv t ∧ a t * thetaDeriv t ≤ 5 / 16 := by
  have ha : 0 ≤ a t := by have := a_lower_of_one_le ht; linarith
  constructor
  · exact mul_nonneg ha (thetaDeriv_nonneg t)
  · exact (mul_le_of_le_one_right ha (thetaDeriv_le t)).trans (a_le_five_sixteenths t)

theorem angularCoeff_sub_abs_le {s t : ℝ} (_hs : 1 ≤ s) (ht : 1 ≤ t) :
    |a s * thetaDeriv s - a t * thetaDeriv t| ≤ (7 / 16) * |s - t| := by
  have ha : 0 ≤ a t := by have := a_lower_of_one_le ht; linarith
  have he : a s * thetaDeriv s - a t * thetaDeriv t =
      (a s - a t) * thetaDeriv s + a t * (thetaDeriv s - thetaDeriv t) := by ring
  calc
    _ ≤ |a s - a t| * |thetaDeriv s| + |a t| * |thetaDeriv s - thetaDeriv t| := by
      rw [he]
      simpa only [abs_mul] using
        abs_add_le ((a s - a t) * thetaDeriv s) (a t * (thetaDeriv s - thetaDeriv t))
    _ = |a s - a t| * thetaDeriv s + a t * |thetaDeriv s - thetaDeriv t| := by
      rw [abs_of_nonneg (thetaDeriv_nonneg s), abs_of_nonneg ha]
    _ ≤ ((1 / 8) * |s - t|) * 1 + (5 / 16) * |s - t| := by
      apply add_le_add
      · exact mul_le_mul (a_sub_abs_le s t) (thetaDeriv_le s)
          (thetaDeriv_nonneg s) (mul_nonneg (by norm_num) (abs_nonneg _))
      · exact mul_le_mul (a_le_five_sixteenths t) (thetaDeriv_sub_abs_le s t)
          (abs_nonneg _) (by norm_num)
    _ = _ := by ring

/-- A global upper speed bound, including the unbounded negative straight tail. -/
theorem gammaDeriv_speed_upper (t : ℝ) : ‖gammaDeriv t‖ ≤ 7 / 16 := by
  by_cases ht : t ≤ 1
  · rw [gammaDeriv_speed_eq_of_le_one ht]
    norm_num
  · have hb := angularCoeff_bounds (le_of_not_ge ht)
    calc
      ‖gammaDeriv t‖ ≤ ‖aDeriv t • v t‖ +
          ‖(a t * thetaDeriv t) • waveDeriv (theta t)‖ := norm_add_le _ _
      _ = aDeriv t + (a t * thetaDeriv t) * ‖waveDeriv (theta t)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (aDeriv_nonneg t), abs_of_nonneg hb.1, v_norm, mul_one]
      _ ≤ 1 / 8 + 5 / 16 := by
        apply add_le_add (aDeriv_le t)
        exact (mul_le_of_le_one_right hb.1 (waveDeriv_norm_le_one _)).trans hb.2
      _ = 7 / 16 := by norm_num

/-- The ordinary mean value estimate applied to the proved derivative. -/
theorem gamma_sub_norm_le_forward (s t : ℝ) : ‖gamma s - gamma t‖ ≤ (7 / 16) * |s - t| := by
  have h : ‖gamma s - gamma t‖ ≤ (7 / 16) * ‖s - t‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (s := (Set.univ : Set ℝ)) (fun x _ => (hasDerivAt_gamma x).hasDerivWithinAt)
      (fun x _ => gammaDeriv_speed_upper x) convex_univ (mem_univ t) (mem_univ s)
  simpa only [Real.norm_eq_abs] using h

theorem gamma_lipschitz : LipschitzWith (7 / 16 : ℝ≥0) gamma := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_div, NNReal.coe_ofNat] using
    gamma_sub_norm_le_forward s t

/-- On the oscillating tail, product differences give the derivative estimate. -/
private theorem gammaDeriv_sub_norm_le_tail {s t : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    ‖gammaDeriv s - gammaDeriv t‖ ≤ |s - t| := by
  have hrad := smul_sub_smul_norm_le (aDeriv s) (aDeriv t) (v s) (v t)
  rw [v_norm, mul_one, abs_of_nonneg (aDeriv_nonneg t)] at hrad
  have hradMul := mul_le_mul (aDeriv_le t) (v_sub_norm_le_forward s t)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hradBound : ‖aDeriv s • v s - aDeriv t • v t‖ ≤ (1 / 4) * |s - t| := by
    linarith [aDeriv_sub_abs_le s t]
  have hb := angularCoeff_bounds ht
  have hwd := (waveDeriv_sub_norm_le (theta s) (theta t)).trans (theta_sub_abs_le s t)
  have hm₁ : |a s * thetaDeriv s - a t * thetaDeriv t| * ‖waveDeriv (theta s)‖ ≤
      (7 / 16) * |s - t| :=
    (mul_le_of_le_one_right (abs_nonneg _) (waveDeriv_norm_le_one _)).trans
      (angularCoeff_sub_abs_le hs ht)
  have hm₂ := mul_le_mul hb.2 hwd (norm_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 5 / 16)
  have hang := smul_sub_smul_norm_le (a s * thetaDeriv s) (a t * thetaDeriv t)
    (waveDeriv (theta s)) (waveDeriv (theta t))
  rw [abs_of_nonneg hb.1] at hang
  have hangBound : ‖(a s * thetaDeriv s) • waveDeriv (theta s) -
      (a t * thetaDeriv t) • waveDeriv (theta t)‖ ≤ (3 / 4) * |s - t| := by
    linarith
  have he : gammaDeriv s - gammaDeriv t =
      (aDeriv s • v s - aDeriv t • v t) +
      ((a s * thetaDeriv s) • waveDeriv (theta s) -
        (a t * thetaDeriv t) • waveDeriv (theta t)) := by
    dsimp [gammaDeriv]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

/-- The constant derivative on the straight tail joins the oscillating estimate at one. -/
theorem gammaDeriv_sub_norm_le_forward (s t : ℝ) :
    ‖gammaDeriv s - gammaDeriv t‖ ≤ |s - t| := by
  have hord : ∀ s t : ℝ, s ≤ t → ‖gammaDeriv s - gammaDeriv t‖ ≤ |s - t| := by
    intro s t hst
    by_cases ht : t ≤ 1
    · rw [gammaDeriv_of_le_one (hst.trans ht), gammaDeriv_of_le_one ht,
        sub_self, norm_zero]
      exact abs_nonneg _
    · have ht1 : 1 ≤ t := (lt_of_not_ge ht).le
      by_cases hs : 1 ≤ s
      · exact gammaDeriv_sub_norm_le_tail hs ht1
      · have hs1 : s ≤ 1 := (lt_of_not_ge hs).le
        calc
          ‖gammaDeriv s - gammaDeriv t‖ = ‖gammaDeriv 1 - gammaDeriv t‖ := by
            rw [gammaDeriv_of_le_one hs1, gammaDeriv_of_le_one (le_refl 1)]
          _ ≤ |1 - t| := gammaDeriv_sub_norm_le_tail (le_refl 1) ht1
          _ ≤ |s - t| := by
            rw [abs_of_nonpos (sub_nonpos.mpr ht1),
              abs_of_nonpos (sub_nonpos.mpr hst)]
            linarith
  rcases le_total s t with hst | hts
  · exact hord s t hst
  · calc
      ‖gammaDeriv s - gammaDeriv t‖ = ‖gammaDeriv t - gammaDeriv s‖ := norm_sub_rev _ _
      _ ≤ |t - s| := hord t s hts
      _ = |s - t| := abs_sub_comm _ _

theorem gammaDeriv_lipschitz : LipschitzWith 1 gammaDeriv := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using
    gammaDeriv_sub_norm_le_forward s t

/-- Normalize the actual nonzero tangent using its proved speed lower bound. -/
theorem u_sub_norm_le_forward (s t : ℝ) : ‖u s - u t‖ ≤ 16 * |s - t| := by
  have hn := normalizeNeg_lipschitz (by norm_num : (0 : ℝ) < 1 / 8)
    (gammaDeriv_speed_lower s) (gammaDeriv_speed_lower t)
  have he : normalizeNeg (gammaDeriv s) - normalizeNeg (gammaDeriv t) =
      -(u s - u t) := by simp only [normalizeNeg, u, neg_sub, neg_sub_neg]
  rw [he, norm_neg, show (2 / (1 / 8 : ℝ)) = 16 by norm_num] at hn
  exact hn.trans (mul_le_mul_of_nonneg_left (gammaDeriv_sub_norm_le_forward s t)
    (by norm_num))

theorem u_lipschitz : LipschitzWith 16 u := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_ofNat] using
    u_sub_norm_le_forward s t

/-- Pairwise estimates with the base parameter first. -/
theorem v_sub_norm_le (s t : ℝ) : ‖v t - v s‖ ≤ |t - s| :=
  v_sub_norm_le_forward t s

theorem gamma_sub_norm_le (s t : ℝ) : ‖gamma t - gamma s‖ ≤ (7 / 16) * |t - s| :=
  gamma_sub_norm_le_forward t s

theorem gammaDeriv_sub_norm_le (s t : ℝ) : ‖gammaDeriv t - gammaDeriv s‖ ≤ |t - s| :=
  gammaDeriv_sub_norm_le_forward t s

theorem u_sub_norm_le (s t : ℝ) : ‖u t - u s‖ ≤ 16 * |t - s| :=
  u_sub_norm_le_forward t s

theorem lipschitzWith_v : LipschitzWith 1 v := v_lipschitz

theorem lipschitzWith_u : LipschitzWith 16 u := u_lipschitz

end ThompsonNonamenability.Analytic

end

end OAI
