import OAI.Geometry.RCD.Sobolev.CutoffErrorLocalization
import OAI.Geometry.RCD.Coordinates.FiniteNormalizerGrowth

namespace OAI

/-! # Actual cutoff Gram budgets from finite-scale harmonic normalization -/

open Set Metric MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace RegularPointCoordinates

def dyadicDirectionConstant (m : ℕ) : ℝ :=
  ((m + 1 : ℕ) : ℝ) ^ 2 + 2 * (((m + 1 : ℕ) : ℝ) ^ 2 * normalizationVolumeRatio m)

theorem dyadicDirectionConstant_nonneg (m : ℕ) : 0 ≤ dyadicDirectionConstant m := by
  have hC := (zero_le_one : (0 : ℝ) ≤ 1).trans (normalizationVolumeRatio_ge_one m)
  unfold dyadicDirectionConstant
  positivity

theorem dyadic_power_volume (n j : ℕ) (r : ℝ) :
    (2 : ℝ) ^ j * (2 ^ j * r) ^ n = (2 ^ (n + 1)) ^ j * r ^ n := by
  rw [mul_pow]
  calc
    _ = ((2 : ℝ) ^ j) ^ (n + 1) * r ^ n := by rw [pow_succ]; ring
    _ = _ := by rw [pow_right_comm]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The same original harmonic column supplies small directional error on
all controlled scales and a fixed raw bound outside them. The cutoff
therefore has a small finite prefix and a Gaussian-summable tail. -/
theorem finite_scale_cutoff_budget {K : ℝ} (m : ℕ) (hX : NoncollapsedRCD K (m + 1) X)
    {a : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m + 1) X) (comparisonModelVolume m a))
    (u : Fin (m + 1) → SobolevSpace (hausdorff (m + 1) X) hX.quadratic)
    (p : X) {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε)
    (hsmall : ((m + 1 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio m * ε) ≤ 1 / 2)
    (A : Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1))
    (hA : IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u) (ball p r) measurableSet_ball A)
    (k : ℕ) (hscale : ∀ j ≤ k, a * (3 * (2 ^ j * r)) ≤ 1)
    (hnormal : ∀ j ≤ k, ∃ (S : Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1))
      (w : X → Euclidean (m + 1)),
      FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic p (2 ^ j * r) ε
        (transformedColumn (hausdorff (m + 1) X) hX.quadratic u S) w ∧
      IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
        (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
        (ball p (2 ^ j * r)) measurableSet_ball S)
    (hroot : sobolevMeanGram (hausdorff (m + 1) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
      (ball p (2 ^ k * r)) measurableSet_ball = ContinuousLinearMap.id ℝ (Euclidean (m + 1)))
    {χ : X → ℝ} (hχ : Continuous χ) (hχrange : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχzero : ∀ x ∉ ball p (2 ^ k * r), χ x = 0)
    {L V : ℝ} (hL : 0 ≤ L) (hV : 0 ≤ V)
    (hvolume : ∀ j ≤ k, 0 < (hausdorff (m + 1) X).real (ball p (2 ^ j * r)) ∧
      hausdorff (m + 1) X (ball p (2 ^ j * r)) ≠ ∞ ∧
      (hausdorff (m + 1) X).real (ball p (2 ^ j * r)) ≤ V * (2 ^ j * r) ^ (m + 1))
    (hgradient : ∀ v : Euclidean (m + 1), ∀ᵐ x ∂(hausdorff (m + 1) X).restrict (ball p (2 ^ k * r)),
      localGamma (hausdorff (m + 1) X) hX.quadratic
        (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u v)
        (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u v) x ≤ L * ‖v‖ ^ 2)
    (v : Euclidean (m + 1)) (j : ℕ) :
    (∫ x in ball p (2 ^ j * r), χ x *
      |localGamma (hausdorff (m + 1) X) hX.quadratic
        (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u (A v))
        (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u (A v)) x - ‖v‖ ^ 2|
          ∂(hausdorff (m + 1) X)) ≤
      (dyadicDirectionConstant m + L + 1) * V * r ^ (m + 1) * ‖v‖ ^ 2 *
        splitSeriesTerm (fun i => ((2 : ℝ) ^ ((m + 1) + 1)) ^ i) ε (k + 1) j := by
  let μ := hausdorff (m + 1) X
  let U := sobolevColumnMap μ hX.quadratic u
  have hC := dyadicDirectionConstant_nonneg m
  have hconst : dyadicDirectionConstant m ≤ dyadicDirectionConstant m + L + 1 := by linarith
  have hconst' : L + 1 ≤ dyadicDirectionConstant m + L + 1 := by linarith
  by_cases hj : j ≤ k
  · have he := (cutoff_error_on_le μ hX.quadratic (U (A v)) (‖v‖ ^ 2)
      (ball p (2 ^ j * r)) (hvolume j hj).2.1 hχ.aestronglyMeasurable hχrange).trans
      (dyadic_normalized_directional_error m hX ha hBG u p hr hε hsmall A hA j
        (fun i hi => hscale i (hi.trans hj)) (fun i hi => hnormal i (hi.trans hj))
        (hvolume j hj).1 (hvolume j hj).2.1 v)
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hvolume j hj).2.2
        (mul_nonneg (mul_nonneg hC hε) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j))) (sq_nonneg ‖v‖)
    change _ ≤ (dyadicDirectionConstant m * ε * 2 ^ j) * _ * _ at he
    have hb := he.trans hm
    have hid : dyadicDirectionConstant m * ε * 2 ^ j *
        (V * (2 ^ j * r) ^ (m + 1)) * ‖v‖ ^ 2 =
        dyadicDirectionConstant m * (V * r ^ (m + 1) * ‖v‖ ^ 2 *
          (ε * ((2 : ℝ) ^ ((m + 1) + 1)) ^ j)) := by
      calc
        _ = (dyadicDirectionConstant m * ε * V * ‖v‖ ^ 2) *
            (2 ^ j * (2 ^ j * r) ^ (m + 1)) := by ring
        _ = _ := by rw [dyadic_power_volume]; ring
    rw [hid] at hb
    have hm' := mul_le_mul_of_nonneg_right hconst
      (show 0 ≤ V * r ^ (m + 1) * ‖v‖ ^ 2 * (ε * ((2 : ℝ) ^ ((m + 1) + 1)) ^ j) by positivity)
    simpa only [splitSeriesTerm, Nat.lt_succ_iff.mpr hj, ite_true, mul_assoc] using hb.trans hm'
  · have hkj : k ≤ j := Nat.le_of_lt (Nat.lt_of_not_ge hj)
    have hpow : (2 : ℝ) ^ k ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hkj
    have hnorm := dyadic_normalizer_norm_sq_bound m hX ha hBG u p hr hε hsmall A hA
      k hscale hnormal hroot
    have hframe := norm_apply_sq_le_of_norm_sq_le (A : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)) hnorm
    have he := (cutoff_error_on_le_total μ hX.quadratic (U (A v)) (‖v‖ ^ 2)
      (hvolume k le_rfl).2.1 hχ.aestronglyMeasurable hχrange hχzero (ball p (2 ^ j * r))).trans
      (cutoff_direction_error_le_raw μ hX.quadratic U A (hvolume k le_rfl).2.1 hχ
        hχrange hχzero hL hgradient hframe v)
    have hcoef : L * 2 ^ k + 1 ≤ (L + 1) * (2 : ℝ) ^ j := by
      have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      nlinarith
    have hvol : μ.real (ball p (2 ^ k * r)) ≤ V * (2 ^ j * r) ^ (m + 1) :=
      (hvolume k le_rfl).2.2.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) k) hr).le
          (mul_le_mul_of_nonneg_right hpow hr.le) (m + 1)) hV)
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul hcoef hvol (measureReal_nonneg : 0 ≤ μ.real (ball p (2 ^ k * r))) (by positivity)) (sq_nonneg ‖v‖)
    have hb := he.trans hm
    have hid : (L + 1) * 2 ^ j * (V * (2 ^ j * r) ^ (m + 1)) * ‖v‖ ^ 2 =
        (L + 1) * (V * r ^ (m + 1) * ‖v‖ ^ 2 * ((2 : ℝ) ^ ((m + 1) + 1)) ^ j) := by
      calc
        _ = ((L + 1) * V * ‖v‖ ^ 2) * (2 ^ j * (2 ^ j * r) ^ (m + 1)) := by ring
        _ = _ := by rw [dyadic_power_volume]; ring
    rw [hid] at hb
    have hm' := mul_le_mul_of_nonneg_right hconst'
      (show 0 ≤ V * r ^ (m + 1) * ‖v‖ ^ 2 * ((2 : ℝ) ^ ((m + 1) + 1)) ^ j by positivity)
    simpa only [splitSeriesTerm, Nat.lt_succ_iff, hj, ite_false, one_mul, mul_assoc] using hb.trans hm'

end RegularPointCoordinates

end

end OAI
