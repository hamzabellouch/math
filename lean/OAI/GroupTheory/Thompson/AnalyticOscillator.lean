import OAI.GroupTheory.Thompson.AnalyticPlaneOscillator
import OAI.GroupTheory.Thompson.AnalyticLpCalculus
import OAI.GroupTheory.Thompson.AnalyticSinc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-!
# The concrete square-integrable oscillator

The representatives are `(cos (z*w), sin (z*w))` and its parameter
derivative `w * (-sin (z*w), cos (z*w))`.  Every passage from a
representative to an `Lp` element uses an almost-everywhere equality.
-/

noncomputable section

namespace ThompsonNonamenability.Analytic

open MeasureTheory Set Filter
open scoped Topology

def waveRep (z w : ℝ) : Plane := planeWave (z * w)

def waveDerivRep (z w : ℝ) : Plane := w • planeDeriv (z * w)

theorem continuous_waveRep (z : ℝ) : Continuous (waveRep z) :=
  continuous_planeWave.comp (continuous_const.mul continuous_id)

theorem continuous_waveDerivRep (z : ℝ) : Continuous (waveDerivRep z) :=
  continuous_id.smul
    (continuous_planeDeriv.comp (continuous_const.mul continuous_id))

theorem waveRep_norm (z w : ℝ) : ‖waveRep z w‖ = 1 :=
  planeWave_norm _

theorem waveDerivRep_norm (z w : ℝ) : ‖waveDerivRep z w‖ = |w| := by
  simp [waveDerivRep, norm_smul, planeDeriv_norm, Real.norm_eq_abs]

theorem waveRep_memLp (z : ℝ) : MemLp (waveRep z) 2 intervalMeasure := by
  apply MemLp.of_bound (continuous_waveRep z).aestronglyMeasurable 1
  exact ae_of_all _ fun w => le_of_eq (waveRep_norm z w)

theorem waveDerivRep_memLp (z : ℝ) : MemLp (waveDerivRep z) 2 intervalMeasure := by
  apply MemLp.of_bound (continuous_waveDerivRep z).aestronglyMeasurable 1
  filter_upwards [ae_restrict_mem measurableSet_Icc] with w hw
  rw [waveDerivRep_norm, abs_of_nonneg hw.1]
  exact hw.2

/-- The oscillator as an actual equivalence class in `L²([0,1]; ℝ²)`. -/
def wave (z : ℝ) : Hilbert := (waveRep_memLp z).toLp (waveRep z)

/-- The proposed derivative, independently defined from its concrete representative. -/
def waveDeriv (z : ℝ) : Hilbert :=
  (waveDerivRep_memLp z).toLp (waveDerivRep z)

theorem wave_coeFn (z : ℝ) : ⇑(wave z) =ᵐ[intervalMeasure] waveRep z :=
  (waveRep_memLp z).coeFn_toLp

theorem waveDeriv_coeFn (z : ℝ) : ⇑(waveDeriv z) =ᵐ[intervalMeasure] waveDerivRep z :=
  (waveDerivRep_memLp z).coeFn_toLp

theorem integral_intervalMeasure (f : ℝ → ℝ) :
    (∫ w, f w ∂intervalMeasure) = ∫ w in (0 : ℝ)..1, f w := by
  change (∫ w in Icc (0 : ℝ) 1, f w) = _
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num)]

theorem integral_cos_intervalMeasure (q : ℝ) :
    (∫ w, Real.cos (q * w) ∂intervalMeasure) = sinc q := by
  rw [integral_intervalMeasure]
  by_cases hq : q = 0
  · simp [hq, sinc_zero]
  · rw [sinc_of_ne_zero hq, intervalIntegral.integral_comp_mul_left _ hq,
      _root_.integral_cos]
    simp [div_eq_mul_inv, mul_comm]

theorem wave_inner (s t : ℝ) : inner (𝕜 := ℝ) (wave s) (wave t) = sinc (t - s) := by
  rw [L2.inner_def]
  calc
    (∫ w, inner (𝕜 := ℝ) (wave s w) (wave t w) ∂intervalMeasure) =
        ∫ w, Real.cos ((t - s) * w) ∂intervalMeasure := by
      apply integral_congr_ae
      filter_upwards [wave_coeFn s, wave_coeFn t] with w hs ht
      rw [hs, ht]
      change inner (𝕜 := ℝ) (planeWave (s * w)) (planeWave (t * w)) =
        Real.cos ((t - s) * w)
      rw [planeWave_inner]
      congr 1
      ring
    _ = sinc (t - s) := integral_cos_intervalMeasure _

theorem wave_norm (z : ℝ) : ‖wave z‖ = 1 := by
  have h := wave_inner z z
  rw [real_inner_self_eq_norm_sq] at h
  simp only [sub_self, sinc_zero] at h
  nlinarith [norm_nonneg (wave z)]

theorem waveDeriv_norm_sq (z : ℝ) : ‖waveDeriv z‖ ^ 2 = 1 / 3 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    (∫ w, inner (𝕜 := ℝ) (waveDeriv z w) (waveDeriv z w) ∂intervalMeasure) =
        ∫ w, w ^ 2 ∂intervalMeasure := by
      apply integral_congr_ae
      filter_upwards [waveDeriv_coeFn z] with w hw
      rw [hw, real_inner_self_eq_norm_sq, waveDerivRep_norm, sq_abs]
    _ = 1 / 3 := by rw [integral_intervalMeasure, _root_.integral_pow]; norm_num

theorem wave_inner_waveDeriv (z : ℝ) : inner (𝕜 := ℝ) (wave z) (waveDeriv z) = 0 := by
  rw [L2.inner_def]
  calc
    (∫ w, inner (𝕜 := ℝ) (wave z w) (waveDeriv z w) ∂intervalMeasure) =
        ∫ _w : ℝ, (0 : ℝ) ∂intervalMeasure := by
      apply integral_congr_ae
      filter_upwards [wave_coeFn z, waveDeriv_coeFn z] with w hw hd
      rw [hw, hd]
      change inner (𝕜 := ℝ) (planeWave (z * w)) (w • planeDeriv (z * w)) = 0
      rw [real_inner_smul_right, planeWave_inner_planeDeriv, mul_zero]
    _ = 0 := integral_zero _ _

theorem waveRep_sub_norm_le (s t w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) :
    ‖waveRep s w - waveRep t w‖ ≤ |s - t| := by
  calc
    ‖waveRep s w - waveRep t w‖ ≤ |s * w - t * w| :=
      planeWave_sub_norm_le _ _
    _ = |s - t| * w := by rw [← sub_mul, abs_mul, abs_of_nonneg hw.1]
    _ ≤ |s - t| := mul_le_of_le_one_right (abs_nonneg _) hw.2

theorem waveDerivRep_sub_norm_le (s t w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) :
    ‖waveDerivRep s w - waveDerivRep t w‖ ≤ |s - t| := by
  have hw2 : w * w ≤ 1 := (mul_le_of_le_one_right hw.1 hw.2).trans hw.2
  calc
    ‖waveDerivRep s w - waveDerivRep t w‖ =
        w * ‖planeDeriv (s * w) - planeDeriv (t * w)‖ := by
      rw [waveDerivRep, waveDerivRep, ← smul_sub, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hw.1]
    _ ≤ w * |s * w - t * w| :=
      mul_le_mul_of_nonneg_left (planeDeriv_sub_norm_le _ _) hw.1
    _ = |s - t| * (w * w) := by
      rw [← sub_mul, abs_mul, abs_of_nonneg hw.1]
      ring
    _ ≤ |s - t| := mul_le_of_le_one_right (abs_nonneg _) hw2

theorem wave_sub_norm_le (s t : ℝ) : ‖wave s - wave t‖ ≤ |s - t| := by
  apply norm_le_of_ae_bound _ (abs_nonneg _)
  filter_upwards [Lp.coeFn_sub (wave s) (wave t), wave_coeFn s, wave_coeFn t,
    ae_restrict_mem measurableSet_Icc] with w hsub hs ht hw
  simpa only [hsub, Pi.sub_apply, hs, ht] using waveRep_sub_norm_le s t w hw

theorem waveDeriv_sub_norm_le (s t : ℝ) :
    ‖waveDeriv s - waveDeriv t‖ ≤ |s - t| := by
  apply norm_le_of_ae_bound _ (abs_nonneg _)
  filter_upwards [Lp.coeFn_sub (waveDeriv s) (waveDeriv t), waveDeriv_coeFn s,
    waveDeriv_coeFn t, ae_restrict_mem measurableSet_Icc] with w hsub hs ht hw
  simpa only [hsub, Pi.sub_apply, hs, ht] using waveDerivRep_sub_norm_le s t w hw

theorem waveRep_remainder (z h w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) :
    ‖waveRep (z + h) w - waveRep z w - h • waveDerivRep z w‖ ≤ |h| ^ 2 := by
  have hscalar : (z + h) * w - z * w = h * w := by ring
  have hrem := planeWave_remainder (z * w) ((z + h) * w)
  rw [hscalar] at hrem
  have hw2 : w ^ 2 ≤ 1 := by nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]
  calc
    ‖waveRep (z + h) w - waveRep z w - h • waveDerivRep z w‖ =
        ‖planeWave ((z + h) * w) - planeWave (z * w) -
          (h * w) • planeDeriv (z * w)‖ := by
      simp only [waveRep, waveDerivRep, mul_smul]
    _ ≤ |h * w| ^ 2 := hrem
    _ = |h| ^ 2 * w ^ 2 := by simp only [abs_mul, mul_pow, sq_abs]
    _ ≤ |h| ^ 2 := mul_le_of_le_one_right (sq_nonneg _) hw2

theorem wave_remainder (z h : ℝ) :
    ‖wave (z + h) - wave z - h • waveDeriv z‖ ≤ |h| ^ 2 := by
  apply norm_le_of_ae_bound _ (sq_nonneg _)
  filter_upwards
    [Lp.coeFn_sub (wave (z + h) - wave z) (h • waveDeriv z),
      Lp.coeFn_sub (wave (z + h)) (wave z), Lp.coeFn_smul h (waveDeriv z),
      wave_coeFn (z + h), wave_coeFn z, waveDeriv_coeFn z,
      ae_restrict_mem measurableSet_Icc] with w ho hi hm hh hz hd hw
  simpa only [ho, hi, hm, Pi.sub_apply, Pi.smul_apply, hh, hz, hd] using
    waveRep_remainder z h w hw

theorem hasDerivAt_wave (z : ℝ) : HasDerivAt wave (waveDeriv z) z := by
  apply hasDerivAt_of_quadratic_remainder (C := 1)
  exact Eventually.of_forall fun h => by simpa using wave_remainder z h

theorem continuous_wave : Continuous wave :=
  Differentiable.continuous (𝕜 := ℝ) (fun z => (hasDerivAt_wave z).differentiableAt)

theorem lipschitzWith_wave : LipschitzWith 1 wave := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  simpa [dist_eq_norm, Real.norm_eq_abs] using wave_sub_norm_le s t

theorem lipschitzWith_waveDeriv : LipschitzWith 1 waveDeriv := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  simpa [dist_eq_norm, Real.norm_eq_abs] using waveDeriv_sub_norm_le s t

theorem continuous_waveDeriv : Continuous waveDeriv := lipschitzWith_waveDeriv.continuous

end ThompsonNonamenability.Analytic

end

end OAI
