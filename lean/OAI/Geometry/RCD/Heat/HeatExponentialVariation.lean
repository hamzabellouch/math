import OAI.Geometry.RCD.Transport.ExponentialTiltLpVariation

namespace OAI

/-! # Relative heat estimates for compact exponential variations -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

 theorem exponentialTiltLp_order (r : Lp ℝ 2 μ) (hr : 0 ≤ r) {g : X → ℝ}
    (hg : Measurable g) {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) (t : ℝ) :
    Real.exp (-|t| *M) • r ≤ exponentialTiltLp μ r hg hgb t ∧
      exponentialTiltLp μ r hg hgb t ≤ Real.exp (|t| *M) • r := by
  have hb (x : X) : -|t| *M ≤ t*g x ∧ t*g x ≤ |t| *M := by
    have h : |t*g x| ≤ |t| *M := by rw [abs_mul]; gcongr; exact hgb x
    simpa only [neg_mul] using abs_le.mp h
  constructor
  · apply (Lp.coeFn_le _ _).mp
    filter_upwards [(Lp.coeFn_nonneg _).mpr hr,exponentialTiltLp_coe μ r hg hgb t,
      Lp.coeFn_smul (Real.exp (-|t| *M)) r] with x hx he hs
    rw [hs,Pi.smul_apply,he]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hb x).1) hx
  · apply (Lp.coeFn_le _ _).mp
    filter_upwards [(Lp.coeFn_nonneg _).mpr hr,exponentialTiltLp_coe μ r hg hgb t,
      Lp.coeFn_smul (Real.exp (|t| *M)) r] with x hx he hs
    rw [hs,Pi.smul_apply,he]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hb x).2) hx

 theorem exponentialTiltLp_remainder_order (r : Lp ℝ 2 μ) (hr : 0 ≤ r) {g : X → ℝ}
    (hg : Measurable g) {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) {t : ℝ} (ht : |t| *M ≤ 1) :
    let v := lpMultiplier μ (boundedMultiplier μ g hg M hgb) r;
    -(t^2*(M:ℝ)^2) • r ≤ exponentialTiltLp μ r hg hgb t-r-t • v ∧
      exponentialTiltLp μ r hg hgb t-r-t • v ≤ (t^2*(M:ℝ)^2) • r := by
  let v := lpMultiplier μ (boundedMultiplier μ g hg M hgb) r
  let w := exponentialTiltLp μ r hg hgb t-r-t • v
  have hv : v =ᵐ[μ] fun x => g x*r x := by
    filter_upwards [lpMultiplier_coe μ (boundedMultiplier μ g hg M hgb) r,
      boundedMultiplier_coe μ g hg M hgb] with x hx hy
    rw [hx,hy]
  have hw : w =ᵐ[μ] fun x => (Real.exp (t*g x)-1-t*g x)*r x := by
    filter_upwards [exponentialTiltLp_coe μ r hg hgb t,hv,
      Lp.coeFn_sub (exponentialTiltLp μ r hg hgb t-r) (t • v),
      Lp.coeFn_sub (exponentialTiltLp μ r hg hgb t) r,Lp.coeFn_smul t v] with x he hx hs hs' hsm
    change (exponentialTiltLp μ r hg hgb t-r-t • v) x = _
    rw [hs,Pi.sub_apply,hs',Pi.sub_apply,hsm,Pi.smul_apply,he,hx]
    change Real.exp (t*g x)*r x-r x-t*(g x*r x) = _
    ring
  have hb : ∀ᵐ x ∂μ, |w x| ≤ (t^2*(M:ℝ)^2)*r x := by
    filter_upwards [hw,(Lp.coeFn_nonneg _).mpr hr] with x hx hp
    have htg : ‖t*g x‖ ≤ |t| *M := by
      rw [norm_mul,Real.norm_eq_abs t,Real.norm_eq_abs (g x)]
      exact mul_le_mul_of_nonneg_left (hgb x) (abs_nonneg t)
    have hsq : ‖t*g x‖^2 ≤ t^2*(M:ℝ)^2 := by
      calc
        _ ≤ (|t| *M)^2 := pow_le_pow_left₀ (norm_nonneg _) htg 2
        _ = _ := by rw [mul_pow,sq_abs]
    rw [hx,abs_mul,abs_of_nonneg hp]
    exact mul_le_mul_of_nonneg_right
      ((Real.norm_exp_sub_one_sub_id_le (htg.trans ht)).trans hsq) hp
  constructor
  · apply (Lp.coeFn_le _ _).mp
    filter_upwards [hb,Lp.coeFn_smul (-(t^2*(M:ℝ)^2)) r] with x hx hs
    change (-(t^2*(M:ℝ)^2) • r) x ≤ w x
    rw [hs,Pi.smul_apply]
    change -(t^2*(M:ℝ)^2)*r x ≤ w x
    linarith [(abs_le.mp hx).1]
  · apply (Lp.coeFn_le _ _).mp
    filter_upwards [hb,Lp.coeFn_smul (t^2*(M:ℝ)^2) r] with x hx hs
    change w x ≤ ((t^2*(M:ℝ)^2) • r) x
    rw [hs,Pi.smul_apply]
    exact (abs_le.mp hx).2

variable [MetricSpace X] [BorelSpace X] [ProperSpace X] [μ.Regular]
  (hQ : QuadraticCheegerEnergy μ)

 theorem heat_exponentialTilt_relative_order (r : Lp ℝ 2 μ) (hr : 0 ≤ r) {g : X → ℝ}
    (hg : Measurable g) {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) (s t : ℝ) :
    Real.exp (-|t| *M) • heatAt μ hQ s r ≤ heatAt μ hQ s (exponentialTiltLp μ r hg hgb t) ∧
      heatAt μ hQ s (exponentialTiltLp μ r hg hgb t) ≤ Real.exp (|t| *M) • heatAt μ hQ s r := by
  have h := exponentialTiltLp_order μ r hr hg hgb t
  exact ⟨by simpa only [map_smul] using heatAt_mono μ hQ s h.1,
    by simpa only [map_smul] using heatAt_mono μ hQ s h.2⟩

 theorem heat_exponentialTilt_remainder_order (r : Lp ℝ 2 μ) (hr : 0 ≤ r) {g : X → ℝ}
    (hg : Measurable g) {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) (s : ℝ) {t : ℝ}
    (ht : |t| *M ≤ 1) :
    let v := heatAt μ hQ s (lpMultiplier μ (boundedMultiplier μ g hg M hgb) r);
    -(t^2*(M:ℝ)^2) • heatAt μ hQ s r ≤
      heatAt μ hQ s (exponentialTiltLp μ r hg hgb t)-heatAt μ hQ s r-t • v ∧
      heatAt μ hQ s (exponentialTiltLp μ r hg hgb t)-heatAt μ hQ s r-t • v ≤
        (t^2*(M:ℝ)^2) • heatAt μ hQ s r := by
  have h := exponentialTiltLp_remainder_order μ r hr hg hgb ht
  exact ⟨by simpa only [map_smul,map_sub] using heatAt_mono μ hQ s h.1,
    by simpa only [map_smul,map_sub] using heatAt_mono μ hQ s h.2⟩

end RegularPointCoordinates

end

end OAI
