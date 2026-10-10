import OAI.Geometry.IsometricImmersion.Pulses.PulseMoment
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Pulse

theorem compact_weight_cos_phase_step {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    {tau : ℝ} (htau : 0 < tau) (phase : ℝ) :
    (∫ x : ℝ, f x*Real.cos (tau*x+phase)) =
      -(∫ x : ℝ, deriv f x*Real.cos (tau*x+(phase-Real.pi/2)))/tau := by
  let v : ℝ → ℝ := fun x => Real.sin (tau*x+phase)/tau
  have hc : Continuous (fun x : ℝ => Real.cos (tau*x+phase)) := by fun_prop
  have hvcont : Continuous v := by dsimp only [v]; fun_prop
  have hdcont : Continuous (deriv f) := (contDiff_infty_iff_deriv.mp hf).2.continuous
  have hdcompact : HasCompactSupport (deriv f) := hcompact.deriv
  have hfc : Integrable (fun x : ℝ => f x*Real.cos (tau*x+phase)) :=
    (hf.continuous.mul hc).integrable_of_hasCompactSupport hcompact.mul_right
  have hdfv : Integrable (fun x : ℝ => deriv f x*v x) :=
    (hdcont.mul hvcont).integrable_of_hasCompactSupport hdcompact.mul_right
  have hfv : Integrable (fun x : ℝ => f x*v x) :=
    (hf.continuous.mul hvcont).integrable_of_hasCompactSupport hcompact.mul_right
  have hv (x : ℝ) : HasDerivAt v (Real.cos (tau*x+phase)) x := by
    have h := ((Real.hasDerivAt_sin (tau*x+phase)).comp x
      (((hasDerivAt_id x).const_mul tau).add_const phase)).div_const tau
    simp only [id_eq,Function.comp_def] at h
    convert h using 1
    field_simp [htau.ne']
  have hibp : (∫ x : ℝ, f x*Real.cos (tau*x+phase)) = -∫ x : ℝ, deriv f x*v x :=
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => (hf.differentiable (by simp) x).hasDerivAt)
      (fun x _ => hv x) hfc hdfv hfv
  have heq : (fun x : ℝ => deriv f x*v x) =
      fun x => (deriv f x*Real.cos (tau*x+(phase-Real.pi/2)))/tau := by
    funext x
    have hp : tau*x+(phase-Real.pi/2) = (tau*x+phase)-Real.pi/2 := by ring
    rw [hp,Real.cos_sub_pi_div_two]
    dsimp only [v]
    ring
  rw [hibp,heq,integral_div]
  ring

theorem compact_weight_cos_phase_order_le (N : ℕ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    {tau : ℝ} (htau : 0 < tau) (phase : ℝ) :
    |∫ x : ℝ, f x*Real.cos (tau*x+phase)| ≤
      (∫ x : ℝ, |iteratedDeriv N f x|)/tau^N := by
  induction N generalizing f phase with
  | zero =>
      have hi : Integrable (fun x : ℝ => |f x|) :=
        hf.continuous.abs.integrable_of_hasCompactSupport hcompact.abs
      have hnorm : ∀ x : ℝ, ‖f x*Real.cos (tau*x+phase)‖ ≤ |f x| := by
        intro x
        simp only [Real.norm_eq_abs,abs_mul]
        exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq (mul_one _)
      simpa only [iteratedDeriv_zero,pow_zero,div_one,Real.norm_eq_abs] using
        norm_integral_le_of_norm_le hi (Eventually.of_forall hnorm)
  | succ N ih =>
      have hdf : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
      have hnext := ih hdf hcompact.deriv (phase-Real.pi/2)
      rw [compact_weight_cos_phase_step hf hcompact htau phase,abs_div,abs_neg,abs_of_pos htau]
      calc
        _ ≤ ((∫ x : ℝ, |iteratedDeriv N (deriv f) x|)/tau^N)/tau :=
          div_le_div_of_nonneg_right hnext htau.le
        _ = _ := by rw [iteratedDeriv_succ',pow_succ]; field_simp [htau.ne']

theorem compact_weight_cos_order_le (N : ℕ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    {tau : ℝ} (htau : 0 < tau) :
    |∫ x : ℝ, f x*Real.cos (tau*x)| ≤ (∫ x : ℝ, |iteratedDeriv N f x|)/tau^N := by
  simpa only [add_zero] using compact_weight_cos_phase_order_le N hf hcompact htau 0

theorem finite_oscillatory_weight_bound (N : ℕ) {f : ℝ → ℝ} {B tau : ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f) (htau : 0 < tau)
    (hB : (∫ x : ℝ, |iteratedDeriv N f x|) ≤ B) :
    |∫ x : ℝ, f x*Real.cos (tau*x)| ≤ B/tau^N :=
  (compact_weight_cos_order_le N hf hcompact htau).trans
    (div_le_div_of_nonneg_right hB (pow_nonneg htau.le N))

end SmoothLocal.Pulse

end

end OAI
