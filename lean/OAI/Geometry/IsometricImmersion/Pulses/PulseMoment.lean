import OAI.Geometry.IsometricImmersion.Pulses.PulseProfiles
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Pulse

theorem compact_weight_cos_integral_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    {tau : ℝ} (htau : 0 < tau) :
    |∫ x : ℝ, f x*Real.cos (tau*x)| ≤ (∫ x : ℝ, |deriv f x|)/tau := by
  let v : ℝ → ℝ := fun x => Real.sin (tau*x)/tau
  have hc : Continuous (fun x : ℝ => Real.cos (tau*x)) := by fun_prop
  have hvcont : Continuous v := by dsimp only [v]; fun_prop
  have hdcont : Continuous (deriv f) := (contDiff_infty_iff_deriv.mp hf).2.continuous
  have hdcompact : HasCompactSupport (deriv f) := hcompact.deriv
  have hfc : Integrable (fun x : ℝ => f x*Real.cos (tau*x)) :=
    (hf.continuous.mul hc).integrable_of_hasCompactSupport hcompact.mul_right
  have hdfv : Integrable (fun x : ℝ => deriv f x*v x) :=
    (hdcont.mul hvcont).integrable_of_hasCompactSupport hdcompact.mul_right
  have hfv : Integrable (fun x : ℝ => f x*v x) :=
    (hf.continuous.mul hvcont).integrable_of_hasCompactSupport hcompact.mul_right
  have hv (x : ℝ) : HasDerivAt v (Real.cos (tau*x)) x := by
    have h := ((Real.hasDerivAt_sin (tau*x)).comp x
      ((hasDerivAt_id x).const_mul tau)).div_const tau
    simp only [Function.comp_def] at h
    convert h using 1
    first | rfl | field_simp [htau.ne']
  have hibp : (∫ x : ℝ, f x*Real.cos (tau*x)) = -∫ x : ℝ, deriv f x*v x :=
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => (hf.differentiable (by simp) x).hasDerivAt)
      (fun x _ => hv x) hfc hdfv hfv
  have hdint : Integrable (fun x : ℝ => |deriv f x|) :=
    hdcont.abs.integrable_of_hasCompactSupport hdcompact.abs
  have hnorm : ∀ x : ℝ, ‖deriv f x*v x‖ ≤ |deriv f x| / tau := by
    intro x
    simp only [Real.norm_eq_abs,abs_mul,v,abs_div,abs_of_pos htau]
    calc
      _ ≤ |deriv f x| * (1/tau) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) htau.le) (abs_nonneg _)
      _ = _ := by ring
  rw [hibp,abs_neg]
  have h := norm_integral_le_of_norm_le (hdint.div_const tau) (Eventually.of_forall hnorm)
  simpa only [Real.norm_eq_abs,integral_div] using h

theorem compact_weight_cos_integral_tendsto_zero {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f) :
    Tendsto (fun tau : ℝ => ∫ x : ℝ, f x*Real.cos (tau*x)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound : ∀ᶠ tau : ℝ in atTop,
      ‖∫ x : ℝ, f x*Real.cos (tau*x)‖ ≤ (∫ x : ℝ, |deriv f x|)/tau := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with tau htau
    simpa only [Real.norm_eq_abs] using compact_weight_cos_integral_le hf hcompact htau
  have hzero : Tendsto (fun tau : ℝ => (∫ x : ℝ, |deriv f x|)/tau) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun tau : ℝ => tau⁻¹) atTop (𝓝 0)).const_mul
        (∫ x : ℝ, |deriv f x|)
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hbound hzero

theorem compact_weight_cos_sq_integral_eq {f : ℝ → ℝ}
    (hf : Continuous f) (hcompact : HasCompactSupport f) (tau : ℝ) :
    (∫ x : ℝ, f x*Real.cos (tau*x)^2) =
      (1/2 : ℝ)*(∫ x : ℝ, f x)+
        (1/2 : ℝ)*(∫ x : ℝ, f x*Real.cos ((2*tau)*x)) := by
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hcompact
  have hci : Integrable (fun x : ℝ => f x*Real.cos ((2*tau)*x)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hcompact.mul_right
  have heq : (fun x : ℝ => f x*Real.cos (tau*x)^2) =
      fun x => (1/2 : ℝ)*f x+(1/2 : ℝ)*(f x*Real.cos ((2*tau)*x)) := by
    funext x
    have hc : Real.cos ((2*tau)*x) = 2*Real.cos (tau*x)^2-1 := by
      rw [mul_assoc,Real.cos_two_mul]
    rw [hc]
    ring
  rw [heq,integral_add (hfi.const_mul (1/2)) (hci.const_mul (1/2)),
    integral_const_mul,integral_const_mul]

theorem compact_weight_cos_sq_integral_tendsto {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f) :
    Tendsto (fun tau : ℝ => ∫ x : ℝ, f x*Real.cos (tau*x)^2) atTop
      (𝓝 ((1/2 : ℝ)*(∫ x : ℝ, f x))) := by
  have hfreq : Tendsto (fun tau : ℝ => 2*tau) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have hzero := (compact_weight_cos_integral_tendsto_zero hf hcompact).comp hfreq
  have hlimit := (hzero.const_mul (1/2 : ℝ)).const_add ((1/2 : ℝ)*(∫ x : ℝ, f x))
  simpa only [compact_weight_cos_sq_integral_eq hf.continuous hcompact,
    Function.comp_def,mul_zero,add_zero] using hlimit

def spatialCutoffSquare (a x : ℝ) : ℝ := axisBump a x^2

theorem spatialCutoffSquare_contDiff (a : ℝ) : ContDiff ℝ ∞ (spatialCutoffSquare a) :=
  (axisBump_contDiff a).pow 2

theorem spatialCutoffSquare_hasCompactSupport {a : ℝ} (ha : 0 < a) :
    HasCompactSupport (spatialCutoffSquare a) := by
  change HasCompactSupport (fun x => axisBump a x ^ 2)
  simpa only [pow_two,Pi.mul_def] using
    (axisBump_hasCompactSupport ha).mul_right (f' := axisBump a)

theorem spatialCutoffSquare_integral_pos {a : ℝ} (ha : 0 < a) :
    0 < ∫ x : ℝ, spatialCutoffSquare a x :=
  (spatialCutoffSquare_contDiff a).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (spatialCutoffSquare_hasCompactSupport ha) (fun _ => sq_nonneg _)
      (sq_pos_of_pos (axisBump_pos_zero ha)).ne'

theorem spatialCutoff_cos_sq_moment_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun tau : ℝ => ∫ x : ℝ, axisBump a x^2*Real.cos (tau*x)^2) atTop
      (𝓝 ((1/2 : ℝ)*(∫ x : ℝ, axisBump a x^2))) :=
  compact_weight_cos_sq_integral_tendsto (spatialCutoffSquare_contDiff a)
    (spatialCutoffSquare_hasCompactSupport ha)

theorem spatialCutoff_cos_sq_moment_eventually_lower {a : ℝ} (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ tau : ℝ in atTop,
      c ≤ ∫ x : ℝ, axisBump a x^2*Real.cos (tau*x)^2 := by
  let I : ℝ := ∫ x : ℝ, axisBump a x^2
  have hI : 0 < I := spatialCutoffSquare_integral_pos ha
  refine ⟨I/4,div_pos hI (by norm_num),?_⟩
  have hgap : I/4 < (1/2 : ℝ)*I := by linarith
  have h := (spatialCutoff_cos_sq_moment_tendsto ha).eventually (eventually_gt_nhds hgap)
  exact h.mono (fun _ ht => ht.le)

end SmoothLocal.Pulse

end

end OAI
