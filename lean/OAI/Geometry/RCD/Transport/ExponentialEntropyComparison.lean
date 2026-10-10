import OAI.Geometry.RCD.Heat.HeatRelativeTangent
import OAI.Geometry.RCD.Transport.RelativeEntropyIntegral

namespace OAI

/-! # Entropy integrability under a two-sided relative exponential bound -/

open Set Filter MeasureTheory
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates

theorem entropy_density_exponential_bound {a r z : ℝ} (hr : 0≤r)
    (hl : Real.exp (-a)*r≤z) (hu : z≤Real.exp a*r) :
    |z*Real.log z|≤Real.exp a*(|r*Real.log r|+a*r) := by
  rcases eq_or_lt_of_le hr with hz | hr
  · have hz0 : z=0 := by rw [←hz,mul_zero] at hl hu; linarith
    simp only [←hz,hz0,zero_mul,mul_zero,abs_zero,add_zero]
    exact le_rfl
  · have hz : 0<z := (mul_pos (Real.exp_pos _) hr).trans_le hl
    have hloglo := Real.log_le_log (mul_pos (Real.exp_pos (-a)) hr) hl
    have hloghi := Real.log_le_log hz hu
    rw [Real.log_mul (Real.exp_ne_zero _) hr.ne',Real.log_exp] at hloglo hloghi
    have hlog : |Real.log z|≤|Real.log r|+a := by
      have he : |Real.log z-Real.log r|≤a := abs_le.mpr ⟨by linarith,by linarith⟩
      calc
        _ = |Real.log r+(Real.log z-Real.log r)| := by congr 1; ring
        _ ≤ |Real.log r|+|Real.log z-Real.log r| := abs_add_le _ _
        _ ≤ _ := add_le_add le_rfl he
    rw [abs_mul,abs_of_pos hz]
    calc
      _ ≤ (Real.exp a*r)*(|Real.log r|+a) := mul_le_mul hu hlog (abs_nonneg _) (by positivity)
      _ = _ := by rw [abs_mul,abs_of_pos hr]; ring

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem entropy_integrable_of_exponential_bound {r z : X → ℝ} {a : ℝ}
    (hz : Measurable z) (hr : ∀ᵐ x ∂μ, 0≤r x)
    (hl : ∀ᵐ x ∂μ, Real.exp (-a)*r x≤z x)
    (hu : ∀ᵐ x ∂μ, z x≤Real.exp a*r x)
    (hi : Integrable r μ) (he : Integrable (fun x => r x*Real.log (r x)) μ) :
    Integrable (fun x => z x*Real.log (z x)) μ := by
  apply ((he.abs.add (hi.const_mul a)).const_mul (Real.exp a)).mono'
    (hz.mul hz.log).aestronglyMeasurable
  filter_upwards [hr,hl,hu] with x hr hl hu
  simpa only [Pi.add_apply,Pi.mul_apply,Real.norm_eq_abs] using
    entropy_density_exponential_bound hr hl hu

variable [MetricSpace X] [BorelSpace X] [ProperSpace X] [μ.Regular]
  (hQ : QuadraticCheegerEnergy μ)

theorem heat_exponential_entropy_integrable (r : Lp ℝ 2 μ) (hr : 0≤r)
    {g : X → ℝ} (hg : Measurable g) {M : ℝ≥0} (hgb : ∀ x, |g x|≤M)
    (s t : ℝ) (hi : Integrable (heatAt μ hQ s r) μ)
    (he : Integrable (fun x => heatAt μ hQ s r x*Real.log (heatAt μ hQ s r x)) μ) :
    Integrable (fun x => heatAt μ hQ s (exponentialTiltLp μ r hg hgb t) x*
      Real.log (heatAt μ hQ s (exponentialTiltLp μ r hg hgb t) x)) μ := by
  obtain ⟨hl,hu⟩ := heat_exponentialTilt_relative_order μ hQ r hr hg hgb s t
  apply entropy_integrable_of_exponential_bound μ (a := |t| * (M:ℝ))
    (Lp.stronglyMeasurable _).measurable ((Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ s r hr))
    ?_ ?_ hi he
  · filter_upwards [(Lp.coeFn_le _ _).mpr hl,
      Lp.coeFn_smul (Real.exp (-|t| * (M:ℝ))) (heatAt μ hQ s r)] with x hx hsm
    rw [hsm,Pi.smul_apply] at hx
    simpa only [neg_mul,smul_eq_mul] using hx
  · filter_upwards [(Lp.coeFn_le _ _).mpr hu,
      Lp.coeFn_smul (Real.exp (|t| * (M:ℝ))) (heatAt μ hQ s r)] with x hx hsm
    simpa only [hsm,Pi.smul_apply,smul_eq_mul] using hx

end RegularPointCoordinates

end

end OAI
