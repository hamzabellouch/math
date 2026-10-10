import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHeatMoments
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace OAI

/-! The nonzero Fourier-mode potential confines mass high in the cusp.
This is the uniform tail estimate for the logarithmic radial model. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaRowHeatScale_lower_bound {h : Eisenstein} (hh : h≠0) :
    4*Real.pi^2/27 ≤ cubicThetaRowHeatScale h := by
  rw [cubicThetaRowHeatScale_eq]
  exact le_mul_of_one_le_right (by positivity) (one_le_norm hh)

private lemma potential_integrable {f : ℝ → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) (A : ℝ) :
    Integrable (fun t : ℝ => A*Real.exp (2*t)*‖f t‖^2) := by
  have hn : HasCompactSupport (fun t : ℝ => ‖f t‖^2) :=
    hc.comp_left (g:=fun z : ℂ => ‖z‖^2) (by simp)
  have hp : HasCompactSupport (fun t : ℝ => A*Real.exp (2*t)*‖f t‖^2) :=
    hn.mul_left
  have ht : Continuous (fun t : ℝ => A*Real.exp (2*t)*‖f t‖^2) := by fun_prop
  exact ht.integrable_of_hasCompactSupport hp

lemma cubicTheta_potential_tail {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    {A : ℝ} (hA : 0<A) (T : ℝ) :
    (∫ t in Ioi T, ‖f t‖^2) ≤ (A*Real.exp (2*T))⁻¹*
      ∫ t : ℝ, A*Real.exp (2*t)*‖f t‖^2 := by
  have hnormC : HasCompactSupport (fun t : ℝ => ‖f t‖^2) :=
    hc.comp_left (g:=fun z : ℂ => ‖z‖^2) (by simp)
  have hnorm : Integrable (fun t : ℝ => ‖f t‖^2) :=
    (hf.norm.pow 2).integrable_of_hasCompactSupport hnormC
  have hp := potential_integrable hf hc A
  have hAe : 0<A*Real.exp (2*T) := mul_pos hA (Real.exp_pos _)
  calc
    _ ≤ ∫ t in Ioi T, (A*Real.exp (2*T))⁻¹*(A*Real.exp (2*t)*‖f t‖^2) := by
      apply integral_mono_ae hnorm.integrableOn (hp.const_mul _).integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht' : T<t := ht
      calc
        _ = (A*Real.exp (2*T))⁻¹*(A*Real.exp (2*T)*‖f t‖^2) := by
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith : 2*T ≤ 2*t)) hA.le)
            (sq_nonneg _)) (inv_nonneg.mpr hAe.le)
    _ = (A*Real.exp (2*T))⁻¹*(∫ t in Ioi T, A*Real.exp (2*t)*‖f t‖^2) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_mono_measure Measure.restrict_le_self
        (ae_of_all _ (fun _ => mul_nonneg (mul_nonneg hA.le (Real.exp_nonneg _)) (sq_nonneg _))) hp)
      (inv_nonneg.mpr hAe.le)

theorem cubicTheta_nonzero_mode_tail {h : Eisenstein} (hh : h≠0)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) (T : ℝ) :
    (∫ t in Ioi T, ‖f t‖^2) ≤
      (27/(4*Real.pi^2)*Real.exp (-2*T))*
        ∫ t : ℝ, cubicThetaRowHeatScale h*Real.exp (2*t)*‖f t‖^2 := by
  have hA := cubicThetaRowHeatScale_pos hh
  have hmin : 0<4*Real.pi^2/27 := by positivity
  have hconstant : (cubicThetaRowHeatScale h*Real.exp (2*T))⁻¹ ≤
      (27/(4*Real.pi^2)*Real.exp (-2*T)) := by
    calc
      _ ≤ ((4*Real.pi^2/27)*Real.exp (2*T))⁻¹ :=
        inv_anti₀ (mul_pos hmin (Real.exp_pos _))
          (mul_le_mul_of_nonneg_right (cubicThetaRowHeatScale_lower_bound hh) (Real.exp_nonneg _))
      _ = _ := by
        rw [mul_inv_rev,show -2*T= -(2*T) by ring,Real.exp_neg]
        field_simp
  exact (cubicTheta_potential_tail hf hc hA T).trans
    (mul_le_mul_of_nonneg_right hconstant
      (integral_nonneg (fun _ => mul_nonneg (mul_nonneg hA.le (Real.exp_nonneg _)) (sq_nonneg _))))

end CubicFirstMoment

end

end OAI
