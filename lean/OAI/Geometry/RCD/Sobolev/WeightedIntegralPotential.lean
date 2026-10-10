import OAI.Analysis.RCDHeat.ExistingAnalytic
import OAI.Geometry.RCD.Sobolev.InnerProductVariation

namespace OAI

/-! # Differentiating a scalar potential against a bounded weight

The L² remainder is controlled by the Lipschitz derivative of the scalar
potential. This permits nonlinear heat pairings without assuming an
L² derivative for their nonlinear factor.
-/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def weightedIntegralPotential (θ : Lp ℝ ∞ μ) (Φ : ℝ → ℝ) (f : Lp ℝ 2 μ) : ℝ :=
  ∫ x, θ x * Φ (f x) ∂μ

theorem weightedIntegralPotential_remainder (θ : Lp ℝ ∞ μ) (B : ℝ≥0)
    (hB : ∀ᵐ x ∂μ, |θ x| ≤ B) {Φ φ : ℝ → ℝ} {C : ℝ≥0}
    (hd : ∀ a, HasDerivAt Φ (φ a) a) (hΦ0 : Φ 0=0)
    (hφ : LipschitzWith C φ) (hφ0 : φ 0=0) (f g : Lp ℝ 2 μ) :
    |weightedIntegralPotential μ θ Φ g - weightedIntegralPotential μ θ Φ f -
      inner ℝ (lpMultiplier μ θ (hφ.compLp hφ0 f)) (g-f)| ≤
      (B:ℝ)*C*‖g-f‖^2 := by
  have hb : ∀ᵐ x ∂μ, ‖θ x‖ ≤ (B:ℝ) := by simpa only [Real.norm_eq_abs] using hB
  have hf := (integralPotential_integrable μ hd hΦ0 hφ hφ0 f).bdd_mul
    (Lp.aestronglyMeasurable θ) hb
  have hg := (integralPotential_integrable μ hd hΦ0 hφ hφ0 g).bdd_mul
    (Lp.aestronglyMeasurable θ) hb
  let l := lpMultiplier μ θ (hφ.compLp hφ0 f)
  have hi := (Lp.memLp l).integrable_mul (Lp.memLp (g-f))
  have he : weightedIntegralPotential μ θ Φ g - weightedIntegralPotential μ θ Φ f -
      inner ℝ l (g-f) = ∫ x, θ x*Φ (g x)-θ x*Φ (f x)-l x*(g-f) x ∂μ := by
    unfold weightedIntegralPotential
    rw [L2.inner_def]
    simp only [Real.inner_apply]
    rw [← integral_sub hg hf]
    exact (integral_sub (hg.sub hf) hi).symm
  rw [he]
  have hrem := ((hg.sub hf).sub hi).abs
  have hsq : Integrable (fun x => ((B:ℝ)*C)*(g-f) x^2) μ := by
    simpa only [Real.norm_eq_abs,sq_abs] using
      ((Lp.memLp (g-f)).integrable_norm_pow (by norm_num : (2:ℕ)≠0)).const_mul ((B:ℝ)*C)
  calc
    _ ≤ ∫ x, |θ x*Φ (g x)-θ x*Φ (f x)-l x*(g-f) x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, ((B:ℝ)*C)*(g-f) x^2 ∂μ := by
      apply integral_mono_ae hrem hsq
      filter_upwards [hB,lpMultiplier_coe μ θ (hφ.compLp hφ0 f),
        hφ.coeFn_compLp hφ0 f,Lp.coeFn_sub g f] with x hbx hl hpf hgf
      change |θ x*Φ (g x)-θ x*Φ (f x)-l x*(g-f) x| ≤ _
      change l x = θ x * (hφ.compLp hφ0 f x) at hl
      rw [hl,hpf,hgf]
      simp only [Pi.sub_apply,Function.comp_apply]
      have hbnd := mul_le_mul hbx (scalar_potential_remainder hd hφ (f x) (g x))
        (abs_nonneg _) B.coe_nonneg
      calc
        _ = |θ x| * |Φ (g x)-Φ (f x)-φ (f x)*(g x-f x)| := by rw [← abs_mul]; congr 1; ring
        _ ≤ _ := hbnd
        _ = _ := by rw [sq_abs]; ring
    _ = _ := by rw [integral_const_mul,integral_sq_Lp]

theorem weightedIntegralPotential_hasFDerivAt (θ : Lp ℝ ∞ μ) (B : ℝ≥0)
    (hB : ∀ᵐ x ∂μ, |θ x| ≤ B) {Φ φ : ℝ → ℝ} {C : ℝ≥0}
    (hd : ∀ a, HasDerivAt Φ (φ a) a) (hΦ0 : Φ 0=0)
    (hφ : LipschitzWith C φ) (hφ0 : φ 0=0) (f : Lp ℝ 2 μ) :
    HasFDerivAt (weightedIntegralPotential μ θ Φ)
      (innerSL ℝ (lpMultiplier μ θ (hφ.compLp hφ0 f))) f := by
  rw [hasFDerivAt_iff_tendsto]
  apply squeeze_zero (fun g => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    (fun g => ?_) (show Tendsto (fun g : Lp ℝ 2 μ => ((B:ℝ)*C)*‖g-f‖) (𝓝 f) (𝓝 0) by
      have hc : Continuous (fun g : Lp ℝ 2 μ => ((B:ℝ)*C)*‖g-f‖) :=
        continuous_const.mul (continuous_id.sub continuous_const).norm
      simpa only [sub_self,norm_zero,mul_zero] using hc.tendsto f)
  have h := mul_le_mul_of_nonneg_left (weightedIntegralPotential_remainder μ θ B hB hd hΦ0 hφ hφ0 f g)
    (inv_nonneg.mpr (norm_nonneg (g-f)))
  have he : ‖g-f‖⁻¹ * (((B:ℝ)*C)*‖g-f‖^2) = ((B:ℝ)*C)*‖g-f‖ := by
    by_cases hz : ‖g-f‖=0
    · simp [hz]
    · field_simp
  simpa only [Real.norm_eq_abs,innerSL_apply_apply,he] using h

end RegularPointCoordinates

end

end OAI
