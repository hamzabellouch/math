import OAI.Geometry.RCD.Heat.HeatExponentialVariation

namespace OAI

/-! # Pointwise relative bounds for the strong heat tangent -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

private theorem lp_relative_order {r v : Lp ℝ 2 μ} {B : ℝ}
    (hl : (-B) • r ≤ v) (hu : v ≤ B • r) : ∀ᵐ x ∂μ, |v x| ≤ B*r x := by
  filter_upwards [(Lp.coeFn_le _ _).mpr hl,(Lp.coeFn_le _ _).mpr hu,
    Lp.coeFn_smul (-B) r,Lp.coeFn_smul B r] with x hl hu hls hus
  rw [hls,Pi.smul_apply] at hl
  rw [hus,Pi.smul_apply] at hu
  apply abs_le.mpr
  constructor
  · change -B*r x ≤ v x at hl
    linarith
  · exact hu

variable [MetricSpace X] [BorelSpace X] [ProperSpace X] [μ.Regular]
  (hQ : QuadraticCheegerEnergy μ)

 theorem heat_exponential_tangent_bound (r : Lp ℝ 2 μ) (hr : 0 ≤ r) {g : X → ℝ}
    (hg : Measurable g) {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) (s : ℝ) :
    ∀ᵐ x ∂μ, |heatAt μ hQ s (lpMultiplier μ (boundedMultiplier μ g hg M hgb) r) x| ≤
      M*heatAt μ hQ s r x := by
  let v := lpMultiplier μ (boundedMultiplier μ g hg M hgb) r
  have hv : v =ᵐ[μ] fun x => g x*r x := by
    filter_upwards [lpMultiplier_coe μ (boundedMultiplier μ g hg M hgb) r,
      boundedMultiplier_coe μ g hg M hgb] with x hx hgx
    rw [hx,hgx]
  have hb : ∀ᵐ x ∂μ, |v x| ≤ M*r x := by
    filter_upwards [hv,(Lp.coeFn_nonneg _).mpr hr] with x hx hp
    rw [hx,abs_mul,abs_of_nonneg hp]
    exact mul_le_mul_of_nonneg_right (hgb x) hp
  have hl : (-(M:ℝ)) • r ≤ v := by
    apply (Lp.coeFn_le _ _).mp
    filter_upwards [hb,Lp.coeFn_smul (-(M:ℝ)) r] with x hx hs
    rw [hs,Pi.smul_apply]
    change -(M:ℝ)*r x ≤ v x
    linarith [(abs_le.mp hx).1]
  have hu : v ≤ (M:ℝ) • r := by
    apply (Lp.coeFn_le _ _).mp
    filter_upwards [hb,Lp.coeFn_smul (M:ℝ) r] with x hx hs
    rw [hs,Pi.smul_apply]
    exact (abs_le.mp hx).2
  apply lp_relative_order μ
  · simpa only [map_smul] using heatAt_mono μ hQ s hl
  · simpa only [map_smul] using heatAt_mono μ hQ s hu

 theorem heat_exponential_remainder_bound (r : Lp ℝ 2 μ) (hr : 0 ≤ r) {g : X → ℝ}
    (hg : Measurable g) {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) (s : ℝ) {t : ℝ}
    (ht : |t| *M ≤ 1) : ∀ᵐ x ∂μ,
    |heatAt μ hQ s (exponentialTiltLp μ r hg hgb t) x-heatAt μ hQ s r x-
      t*heatAt μ hQ s (lpMultiplier μ (boundedMultiplier μ g hg M hgb) r) x| ≤
        (M:ℝ)^2*t^2*heatAt μ hQ s r x := by
  let R := heatAt μ hQ s r
  let F := heatAt μ hQ s (exponentialTiltLp μ r hg hgb t)
  let V := heatAt μ hQ s (lpMultiplier μ (boundedMultiplier μ g hg M hgb) r)
  have h := heat_exponentialTilt_remainder_order μ hQ r hr hg hgb s ht
  have hb := lp_relative_order μ h.1 h.2
  filter_upwards [hb,Lp.coeFn_sub (F-R) (t • V),Lp.coeFn_sub F R,Lp.coeFn_smul t V] with x hx hsub hsub' hsm
  change |(F-R-t • V) x| ≤ (t^2*(M:ℝ)^2)*R x at hx
  rw [hsub,Pi.sub_apply,hsub',Pi.sub_apply,hsm,Pi.smul_apply] at hx
  change |F x-R x-t*V x| ≤ _ at hx
  convert hx using 1
  ring

 theorem heat_exponential_nonneg (r : Lp ℝ 2 μ) (hr : 0 ≤ r) {g : X → ℝ}
    (hg : Measurable g) {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) (s t : ℝ) :
    0 ≤ heatAt μ hQ s (exponentialTiltLp μ r hg hgb t) := by
  apply heatAt_nonneg
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [exponentialTiltLp_coe μ r hg hgb t,(Lp.coeFn_nonneg _).mpr hr] with x hx hp
  rw [hx]
  exact mul_nonneg (Real.exp_pos _).le hp

 theorem heat_exponential_power_integrable (r : Lp ℝ 2 μ) (hr : 0 ≤ r) {g : X → ℝ}
    (hg : Measurable g) {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) (s t : ℝ) {q : ℝ}
    (hq : 0 ≤ q) (hi : Integrable (fun x => (heatAt μ hQ s r x)^q) μ) :
    Integrable (fun x => (heatAt μ hQ s (exponentialTiltLp μ r hg hgb t) x)^q) μ := by
  have hpos := (Lp.coeFn_nonneg _).mpr (heat_exponential_nonneg μ hQ r hr hg hgb s t)
  have hbase := (Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ s r hr)
  have hu := (Lp.coeFn_le _ _).mpr (heat_exponentialTilt_relative_order μ hQ r hr hg hgb s t).2
  apply (hi.const_mul ((Real.exp (|t| *M))^q)).mono'
    ((Lp.stronglyMeasurable _).measurable.pow_const q).aestronglyMeasurable
  filter_upwards [hpos,hbase,hu,Lp.coeFn_smul (Real.exp (|t| *M)) (heatAt μ hQ s r)] with x hp hb hu hs
  rw [hs,Pi.smul_apply] at hu
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hp _)]
  calc
    _ ≤ (Real.exp (|t| *M)*heatAt μ hQ s r x)^q := Real.rpow_le_rpow hp hu hq
    _ = _ := Real.mul_rpow (Real.exp_pos _).le hb

end RegularPointCoordinates

end

end OAI
