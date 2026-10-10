import OAI.Geometry.RCD.Heat.HeatEntropyVariation
import OAI.Geometry.RCD.Coordinates.NormalizedTiltLpVariation

namespace OAI

/-! # The entropy response of the normalized heat perturbation -/

open Set Filter MeasureTheory
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates

theorem entropy_density_mul {a r : ℝ} (ha : 0<a) (hr : 0≤r) :
    (a*r)*Real.log (a*r)=a*(r*Real.log r)+(a*Real.log a)*r := by
  have h := entropy_density_scale ha (mul_nonneg ha.le hr)
  rw [mul_div_cancel_left₀ r ha.ne'] at h
  convert h using 1
  ring

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem exponentialTiltLp_integrable (r : Lp ℝ 2 μ) (hi : Integrable r μ)
    {g : X → ℝ} (hg : Measurable g) {M : ℝ≥0} (hgb : ∀ x, |g x|≤M) (t : ℝ) :
    Integrable (exponentialTiltLp μ r hg hgb t) μ := by
  have hb : ∀ᵐ x ∂μ, ‖Real.exp (t*g x)‖≤Real.exp (|t| * (M:ℝ)) :=
    .of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      exact (le_abs_self _).trans (by rw [abs_mul]; gcongr; exact hgb x)
  exact (hi.bdd_mul (hg.const_mul t |>.exp.aestronglyMeasurable) hb).congr
    (exponentialTiltLp_coe μ r hg hgb t).symm

theorem integral_entropy_mul {a : ℝ} {r : X → ℝ} (ha : 0<a)
    (hr : ∀ᵐ x ∂μ, 0≤r x) (hi : Integrable r μ)
    (he : Integrable (fun x => r x*Real.log (r x)) μ) :
    (∫ x, (a*r x)*Real.log (a*r x) ∂μ)=
      a*(∫ x, r x*Real.log (r x) ∂μ)+(a*Real.log a)*(∫ x, r x ∂μ) := by
  rw [integral_congr_ae (hr.mono fun x hx => entropy_density_mul ha hx),
    integral_add (he.const_mul _) (hi.const_mul _),integral_const_mul,integral_const_mul]

variable [MetricSpace X] [BorelSpace X] [ProperSpace X] [μ.Regular]
  (hQ : QuadraticCheegerEnergy μ)

theorem heat_normalized_entropy_hasDerivAt_zero (r : Lp ℝ 2 μ) (hr : 0≤r)
    (hri : Integrable r μ) (hm : (∫ x, r x ∂μ)=1)
    {g : X → ℝ} (hg : Measurable g) {M : ℝ≥0} (hgb : ∀ x, |g x|≤M)
    (s : ℝ)
    (he : Integrable (fun x => heatAt μ hQ s r x*Real.log (heatAt μ hQ s r x)) μ)
    (hmass : ∀ t : ℝ, (∫ x, heatAt μ hQ s (exponentialTiltLp μ r hg hgb t) x ∂μ)=
      ∫ x, Real.exp (t*g x)*r x ∂μ) :
    HasDerivAt (fun t : ℝ => ∫ x, heatAt μ hQ s (normalizedTiltLp μ r hg hgb t) x*
      Real.log (heatAt μ hQ s (normalizedTiltLp μ r hg hgb t) x) ∂μ)
      ((∫ x, (1+Real.log (heatAt μ hQ s r x))*
        heatAt μ hQ s (lpMultiplier μ (boundedMultiplier μ g hg M hgb) r) x ∂μ)-
        (∫ x, g x*r x ∂μ)*((∫ x, heatAt μ hQ s r x*Real.log (heatAt μ hQ s r x) ∂μ)+1)) 0 := by
  let Z := fun t : ℝ => ∫ x, Real.exp (t*g x)*r x ∂μ
  have hZ : HasDerivAt Z (∫ x, g x*r x ∂μ) 0 :=
    exponential_tilt_integral_hasDerivAt_zero μ hri hg hgb
  have hZ0 : Z 0=1 := by simpa only [Z,zero_mul,Real.exp_zero,one_mul] using hm
  have hZn : Z 0≠0 := by rw [hZ0]; exact one_ne_zero
  have hW := heat_exponential_entropy_hasDerivAt_zero μ hQ r hr hri hg hgb s he
  have hD := ((hZ.inv hZn).mul hW).sub (hZ.log hZn)
  have hD' : HasDerivAt
      (fun t : ℝ => (Z t)⁻¹*(∫ x, heatAt μ hQ s (exponentialTiltLp μ r hg hgb t) x*
        Real.log (heatAt μ hQ s (exponentialTiltLp μ r hg hgb t) x) ∂μ)-Real.log (Z t))
      ((∫ x, (1+Real.log (heatAt μ hQ s r x))*
        heatAt μ hQ s (lpMultiplier μ (boundedMultiplier μ g hg M hgb) r) x ∂μ)-
        (∫ x, g x*r x ∂μ)*((∫ x, heatAt μ hQ s r x*Real.log (heatAt μ hQ s r x) ∂μ)+1)) 0 := by
    convert hD using 1
    simp only [Pi.inv_apply,hZ0,inv_one,one_pow,div_one,one_mul,exponentialTiltLp_zero]
    ring
  apply hD'.congr_of_eventuallyEq
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, 0<Z t :=
    hZ.continuousAt.tendsto.eventually (Ioi_mem_nhds (by rw [hZ0]; norm_num))
  filter_upwards [hnear] with t ht
  have hn : heatAt μ hQ s (normalizedTiltLp μ r hg hgb t)=
      (Z t)⁻¹ • heatAt μ hQ s (exponentialTiltLp μ r hg hgb t) := map_smul _ _ _
  rw [hn]
  have hrep := Lp.coeFn_smul (Z t)⁻¹ (heatAt μ hQ s (exponentialTiltLp μ r hg hgb t))
  have hi := heatAt_integrable μ hQ s (exponentialTiltLp μ r hg hgb t)
    (exponentialTiltLp_integrable μ r hri hg hgb t)
  have hrep' : (fun x => ((Z t)⁻¹ • heatAt μ hQ s (exponentialTiltLp μ r hg hgb t)) x*
      Real.log (((Z t)⁻¹ • heatAt μ hQ s (exponentialTiltLp μ r hg hgb t)) x)) =ᵐ[μ]
      fun x => ((Z t)⁻¹*heatAt μ hQ s (exponentialTiltLp μ r hg hgb t) x)*
        Real.log ((Z t)⁻¹*heatAt μ hQ s (exponentialTiltLp μ r hg hgb t) x) := by
    filter_upwards [hrep] with x hx
    simp only [Pi.smul_apply,smul_eq_mul] at hx
    rw [hx]
  rw [integral_congr_ae hrep']
  rw [integral_entropy_mul μ (inv_pos.mpr ht)
    ((Lp.coeFn_nonneg _).mpr (heat_exponential_nonneg μ hQ r hr hg hgb s t)) hi
    (heat_exponential_entropy_integrable μ hQ r hr hg hgb s t (heatAt_integrable μ hQ s r hri) he),hmass]
  change (Z t)⁻¹*_+((Z t)⁻¹*Real.log (Z t)⁻¹)*(Z t)=_
  rw [Real.log_inv]
  field_simp
  ring

end RegularPointCoordinates

end

end OAI
