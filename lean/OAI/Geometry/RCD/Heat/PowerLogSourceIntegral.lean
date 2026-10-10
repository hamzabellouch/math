import OAI.Geometry.RCD.Sobolev.SobolevPowerGammaIntegrable
import OAI.Geometry.RCD.Sobolev.SobolevPowerSourceIntegrable

namespace OAI

/-! # Integrating the logarithmic source after cancellation of denominators -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates

theorem power_log_source_algebra {U V d g κ H : ℝ} (hU : 0 ≤ U) (hV : 0 < V)
    (h : -H ≤ κ*(d/V-g/V^2)) (n : ℕ) :
    κ*(U^(n+2)*V^n*g-V^(n+1)*U^(n+2)*d) ≤ (U*V)^(n+2)*H := by
  have hm := mul_le_mul_of_nonneg_left h (pow_nonneg (mul_nonneg hU hV.le) (n+2))
  have he : (U*V)^(n+2)*(κ*(d/V-g/V^2)) =
      κ*(V^(n+1)*U^(n+2)*d-U^(n+2)*V^n*g) := by
    field_simp
    simp only [mul_pow,pow_add,pow_one,pow_two]
    ring
  rw [he] at hm
  nlinarith only [hm]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem power_log_source_integral (u v : SobolevSpace μ Q) (e : Lp ℝ 2 μ)
    (A B : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q u x| ≤ A)
    (hv : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q v x| ≤ B)
    (hu0 : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ Q u x)
    (hv0 : ∀ᵐ x ∂μ, 0 < SobolevSpace.toLp μ Q v x)
    (κ : ℝ) (H : X → ℝ) (n : ℕ)
    (hH : Integrable (fun x => (SobolevSpace.toLp μ Q u x*
      SobolevSpace.toLp μ Q v x)^(n+2)*H x) μ)
    (hlog : ∀ᵐ x ∂μ, -H x ≤ κ*(e x/SobolevSpace.toLp μ Q v x-
      localGamma μ Q v v x/(SobolevSpace.toLp μ Q v x)^2)) :
    κ*((∫ x, (SobolevSpace.toLp μ Q u x)^(n+2)*(SobolevSpace.toLp μ Q v x)^n*
      localGamma μ Q v v x ∂μ)-
      (∫ x, (SobolevSpace.toLp μ Q v x)^(n+1)*(SobolevSpace.toLp μ Q u x)^(n+2)*e x ∂μ)) ≤
    ∫ x, (SobolevSpace.toLp μ Q u x*SobolevSpace.toLp μ Q v x)^(n+2)*H x ∂μ := by
  have ha := sobolev_power_gamma_integrable μ Q u v v v A B hu hv (n+2) n
  have hi := sobolev_power_product_source_integrable μ Q u v e A B hu hv (n+1) n
  simp only [Nat.add_assoc,show (1:ℕ)+1 = 2 from rfl] at hi
  have hle := integral_mono_ae ((ha.sub hi).const_mul κ) hH
    (by filter_upwards [hu0,hv0,hlog] with x hu0x hv0x hx
        exact power_log_source_algebra hu0x hv0x hx n)
  rw [integral_const_mul] at hle
  simp only [Pi.sub_apply] at hle
  rwa [integral_sub ha hi] at hle

end RegularPointCoordinates

end

end OAI
