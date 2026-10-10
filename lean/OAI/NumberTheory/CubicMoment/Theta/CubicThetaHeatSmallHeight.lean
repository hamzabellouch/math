import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHeatScaling
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! At small height the normalized nonzero-frequency heat integral tends
to the ordinary Gamma integral. This supplies nonvanishing without any
assumption on special-function zeros. -/
noncomputable section
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

def cubicThetaNormalizedHeat (s : ℂ) (A v t : ℝ) : ℂ :=
  (Real.exp (-t):ℂ)*(t:ℂ)^(s-2)*(Real.exp (-A*v^2/t):ℂ)

lemma cubicThetaNormalizedHeat_bound (s : ℂ) {A : ℝ} (hA : 0≤A)
    (v : ℝ) {t : ℝ} (ht : 0<t) :
    ‖cubicThetaNormalizedHeat s A v t‖≤‖(Real.exp (-t):ℂ)*(t:ℂ)^(s-2)‖ := by
  unfold cubicThetaNormalizedHeat
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (_root_.norm_nonneg _)
    (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hA) (sq_nonneg v)) ht.le))

theorem cubicThetaNormalizedHeat_gamma_limit {s : ℂ} (hs : 1<s.re)
    {A : ℝ} (hA : 0≤A) :
    Tendsto (fun v : ℝ => ∫ t in Ioi (0:ℝ), cubicThetaNormalizedHeat s A v t)
      (𝓝 0) (𝓝 (Complex.Gamma (s-1))) := by
  have hg : IntegrableOn (fun t : ℝ => (Real.exp (-t):ℂ)*(t:ℂ)^(s-2)) (Ioi 0) := by
    simpa only [show s-1-1=s-2 by ring] using
      Complex.GammaIntegral_convergent (s:=s-1) (by simp; linarith)
  have hl := tendsto_integral_filter_of_dominated_convergence
    (μ:=volume.restrict (Ioi (0:ℝ)))
    (fun t : ℝ => ‖(Real.exp (-t):ℂ)*(t:ℂ)^(s-2)‖)
    (Filter.Eventually.of_forall (fun v : ℝ => show
      AEStronglyMeasurable (cubicThetaNormalizedHeat s A v) (volume.restrict (Ioi 0)) from by
        apply Measurable.aestronglyMeasurable
        unfold cubicThetaNormalizedHeat
        fun_prop))
    (Filter.Eventually.of_forall (fun v : ℝ => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact cubicThetaNormalizedHeat_bound s hA v ht)) hg.norm
    (show ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), Tendsto
        (fun v : ℝ => cubicThetaNormalizedHeat s A v t) (𝓝 0)
        (𝓝 ((Real.exp (-t):ℂ)*(t:ℂ)^(s-2))) from by
      filter_upwards with t
      have hc : ContinuousAt (fun v : ℝ => cubicThetaNormalizedHeat s A v t) 0 := by
        unfold cubicThetaNormalizedHeat
        fun_prop
      simpa only [cubicThetaNormalizedHeat,zero_pow (by norm_num : (2:ℕ)≠0),
        mul_zero,zero_div,Real.exp_zero,Complex.ofReal_one,mul_one] using hc.tendsto)
  convert hl using 1
  rw [Complex.Gamma_eq_integral (by simp; linarith),Complex.GammaIntegral]
  simp only [show s-1-1=s-2 by ring]

end CubicFirstMoment

end

end OAI
