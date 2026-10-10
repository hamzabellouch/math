import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialEnergyNorm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! The one-dimensional H1 modulus of continuity, derived from the
fundamental theorem of calculus and Hilbert-space Cauchy--Schwarz. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicTheta_integral_sq_bound {μ : Measure ℝ} [IsFiniteMeasure μ]
    {f : ℝ → ℂ} (hf : MemLp f 2 μ) :
    ‖∫ t, f t ∂μ‖^2 ≤ μ.real univ*(∫ t, ‖f t‖^2 ∂μ) := by
  let F := hf.toLp f
  have hC : MemLp (fun _ : ℝ => (1:ℂ)) 2 μ := memLp_const 1
  let C := hC.toLp (fun _ : ℝ => (1:ℂ))
  have hinner : inner ℂ C F=∫ t, f t ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hC.coeFn_toLp,hf.coeFn_toLp] with t ht hu
    change inner ℂ (C t) (F t)=f t
    rw [ht,hu]
    simp [RCLike.inner_apply]
  have hCN : ‖C‖^2=μ.real univ := by
    rw [cubicTheta_l2_norm_sq_measure]
    calc
      _ = ∫ _ : ℝ, (1:ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hC.coeFn_toLp] with t ht
        change ‖C t‖^2=1
        rw [ht]
        simp
      _ = _ := by simp
  have hFN : ‖F‖^2=∫ t, ‖f t‖^2 ∂μ := by
    rw [cubicTheta_l2_norm_sq_measure]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with t ht
    change ‖F t‖^2=‖f t‖^2
    rw [ht]
  calc
    _ = ‖inner ℂ C F‖^2 := by rw [hinner]
    _ ≤ (‖C‖*‖F‖)^2 := pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_inner_le_norm C F) 2
    _ = ‖C‖^2*‖F‖^2 := mul_pow _ _ _
    _ = _ := by rw [hCN,hFN]

theorem cubicTheta_radial_holder_sq {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) {a b : ℝ} (hab : a ≤ b) :
    ‖f b-f a‖^2 ≤ (b-a)*(∫ t : ℝ, ‖deriv f t‖^2) := by
  let μ : Measure ℝ := volume.restrict (Ioc a b)
  have hdc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hdI : Integrable (deriv f) := hdc.integrable_of_hasCompactSupport hc.deriv
  have hdLp : MemLp (deriv f) 2 volume := hdc.memLp_of_hasCompactSupport hc.deriv
  have hμLp : MemLp (deriv f) 2 μ := hdLp.mono_measure Measure.restrict_le_self
  have hμ : μ.real univ=b-a := by
    simp [μ,measureReal_def,Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  have hi : (∫ t, deriv f t ∂μ)=f b-f a := by
    rw [← intervalIntegral.integral_of_le hab]
    exact intervalIntegral.integral_deriv_eq_sub (fun t _ => hf.differentiable (by norm_num) t)
      hdI.intervalIntegrable
  calc
    _ = ‖∫ t, deriv f t ∂μ‖^2 := by rw [hi]
    _ ≤ μ.real univ*(∫ t, ‖deriv f t‖^2 ∂μ) := cubicTheta_integral_sq_bound hμLp
    _ ≤ _ := by
      rw [hμ]
      apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hab)
      exact integral_mono_measure Measure.restrict_le_self
        (ae_of_all _ (fun _ => sq_nonneg _))
        ((memLp_two_iff_integrable_sq_norm hdLp.aestronglyMeasurable).mp hdLp)

end CubicFirstMoment

end

end OAI
