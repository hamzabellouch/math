import Mathlib
import OAI.Probability.SLELocalization.CommonClocks

namespace OAI


/-! Conformal localization and Rectangle Energy estimates. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy
open Layer

lemma circle_derivative_square {u : ℂ → ℝ} (hu : ContDiffOn ℝ 2 u (ball 0 1))
    {r : ℝ} (hr : |r| < 1) :
    (circleDMean u r)^2 ≤ (2*Real.pi)*(∫ θ in -Real.pi..Real.pi,
      ‖fderiv ℝ u (r • circleMap 0 1 θ)‖^2) := by
  let D := fun θ : ℝ => fderiv ℝ u (r • circleMap 0 1 θ) (circleMap 0 1 θ)
  have hdu : ContDiffOn ℝ 1 (fderiv ℝ u) (ball 0 1) :=
    hu.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hgrad : Continuous (fun θ : ℝ => fderiv ℝ u (r • circleMap 0 1 θ)) := by
    apply continuousOn_univ.1
    exact hdu.continuousOn.comp ((continuous_circleMap 0 1).const_smul r).continuousOn
      (fun θ _ => radial_mem hr θ)
  have hD : Continuous D := hgrad.clm_apply (continuous_circleMap 0 1)
  have hp : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hc := integral_mul_square_le (continuousOn_memLp_two_Ioc hp hD.continuousOn)
    (continuousOn_memLp_two_Ioc hp (continuous_const (y := (1:ℝ))).continuousOn)
  have heD : (∫ θ in Ioc (-Real.pi) Real.pi, D θ*1) = circleDMean u r := by
    simp only [mul_one,circleDMean,intervalIntegral.integral_of_le hp,D]
  have he1 : (∫ θ in Ioc (-Real.pi) Real.pi, (1:ℝ)^2) = 2*Real.pi := by
    rw [← intervalIntegral.integral_of_le hp]
    simp
    ring
  rw [heD,he1] at hc
  have hle : (∫ θ in Ioc (-Real.pi) Real.pi, D θ^2) ≤
      ∫ θ in -Real.pi..Real.pi, ‖fderiv ℝ u (r • circleMap 0 1 θ)‖^2 := by
    rw [intervalIntegral.integral_of_le hp]
    apply integral_mono_ae ((hD.pow 2).intervalIntegrable _ _).1
      ((hgrad.norm.pow 2).intervalIntegrable _ _).1
    filter_upwards with θ
    have hb := (fderiv ℝ u (r • circleMap 0 1 θ)).le_opNorm (circleMap 0 1 θ)
    norm_num only [norm_circleMap_zero,abs_one,mul_one] at hb
    have hh := pow_le_pow_left₀ (norm_nonneg _) hb 2
    simpa only [Real.norm_eq_abs,sq_abs,D,Pi.pow_apply] using hh
  exact hc.trans (by nlinarith [Real.pi_pos])

theorem critical_circle_means {u : ℂ → ℝ} (hu : ContDiffOn ℝ 2 u (ball 0 1))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    (circleMean u b-circleMean u a)^2 ≤ 2*Real.pi*Real.log (b/a)*
      (∫ s in a..b, s*(∫ θ in -Real.pi..Real.pi, ‖fderiv ℝ u (s • circleMap 0 1 θ)‖^2)) := by
  have hs (s : ℝ) (hs : s ∈ Icc a b) : |s| < 1 :=
    abs_lt.2 ⟨by linarith [hs.1],hs.2.trans_lt hb⟩
  have hD : ContinuousOn (circleDMean u) (Icc a b) := by
    intro s hs'
    exact ((circle_means_derivatives hu (hs s hs')).2.continuousAt).continuousWithinAt
  have ht := weighted_interval_energy ha hab hD
    (fun s hs' => (circle_means_derivatives hu (hs s hs')).1)
  let E := fun s : ℝ => ∫ θ in -Real.pi..Real.pi, ‖fderiv ℝ u (s • circleMap 0 1 θ)‖^2
  let h := (b+1)/2
  have hh : h < 1 := by dsimp [h]; linarith
  have hbh : b < h := by dsimp [h]; linarith
  have hdu : ContDiffOn ℝ 1 (fderiv ℝ u) (ball 0 1) :=
    hu.fderiv_of_isOpen isOpen_ball (by norm_num)
  have henergy : ContinuousOn (fun p : ℝ × ℝ => ‖fderiv ℝ u (p.1 • circleMap 0 1 p.2)‖^2)
      (Icc 0 h ×ˢ Icc (-Real.pi) Real.pi) :=
    (hdu.continuousOn.comp radial_continuous.continuousOn
      (radial_interval_maps (by norm_num) hh)).norm.pow 2
  have hE : ContinuousOn E (Icc a b) := by
    intro s hs'
    exact (compact_parameter_continuousAt (F := fun s θ => ‖fderiv ℝ u (s • circleMap 0 1 θ)‖^2)
      (by linarith [Real.pi_pos])
      (ha.trans_le hs'.1) (hs'.2.trans_lt hbh) henergy).continuousWithinAt
  have hle : (∫ s in a..b, s*(circleDMean u s)^2) ≤
      ∫ s in a..b, (2*Real.pi)*(s*E s) := by
    apply intervalIntegral.integral_mono_on hab
      ((continuousOn_id.mul (hD.pow 2)).intervalIntegrable_of_Icc hab)
      ((continuousOn_const.mul (continuousOn_id.mul hE)).intervalIntegrable_of_Icc hab)
    intro s hs'
    have hc := mul_le_mul_of_nonneg_left (circle_derivative_square hu (hs s hs'))
      (ha.trans_le hs'.1).le
    dsimp only [E]
    exact hc.trans_eq (by simp only [Pi.mul_apply,id_eq]; ring)
  have hl : 0 ≤ Real.log (b/a) := Real.log_nonneg ((one_le_div ha).2 hab)
  have hh' := mul_le_mul_of_nonneg_left hle hl
  rw [intervalIntegral.integral_const_mul] at hh'
  apply ht.trans
  convert hh' using 1
  ring

end SLEExactGauge.RectangleEnergy

end

end OAI
