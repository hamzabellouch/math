import OAI.Geometry.RCD.Sobolev.PowerEnergyRates
import OAI.Geometry.RCD.Sobolev.PowerEnergyComparison
import OAI.Geometry.RCD.Heat.PowerLogSourceIntegral

namespace OAI

/-! # The density-power rate bound from the actual logarithmic source -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem power_rate_le_of_log_source (u v : SobolevSpace μ Q) (d e : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ Q u d) (he : IsWeakLaplacian μ Q v e) (A B : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q u x| ≤ A)
    (hv : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q v x| ≤ B)
    (hu0 : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ Q u x)
    (hv0 : ∀ᵐ x ∂μ, 0 < SobolevSpace.toLp μ Q v x)
    {κ : ℝ} (hκ : 0 ≤ κ) (H : X → ℝ) (n : ℕ)
    (hH : Integrable (fun x => (SobolevSpace.toLp μ Q u x*
      SobolevSpace.toLp μ Q v x)^(n+2)*H x) μ)
    (hlog : ∀ᵐ x ∂μ, -H x ≤ κ*(e x/SobolevSpace.toLp μ Q v x-
      localGamma μ Q v v x/(SobolevSpace.toLp μ Q v x)^2)) :
    (κ/2)*(n+2:ℝ)*(∫ x, (SobolevSpace.toLp μ Q u x*SobolevSpace.toLp μ Q v x)^(n+1)*
      (d x*SobolevSpace.toLp μ Q v x-SobolevSpace.toLp μ Q u x*e x) ∂μ) ≤
    (n+1:ℝ)*(∫ x, (SobolevSpace.toLp μ Q u x*SobolevSpace.toLp μ Q v x)^(n+2)*H x ∂μ) := by
  let a := ∫ x, (SobolevSpace.toLp μ Q u x)^(n+2)*(SobolevSpace.toLp μ Q v x)^n*
    localGamma μ Q v v x ∂μ
  let b := ∫ x, (SobolevSpace.toLp μ Q v x)^(n+2)*(SobolevSpace.toLp μ Q u x)^n*
    localGamma μ Q u u x ∂μ
  let c := ∫ x, (SobolevSpace.toLp μ Q u x)^(n+1)*(SobolevSpace.toLp μ Q v x)^(n+1)*
    localGamma μ Q u v x ∂μ
  have hsource := power_log_source_integral μ Q u v e A B hu hv hu0 hv0 κ H n hH hlog
  rw [weakLaplacian_log_power_balance μ Q u v e he A B hu hv n] at hsource
  have hbound : κ*(n+2:ℝ)*(a+c) ≤
      ∫ x, (SobolevSpace.toLp μ Q u x*SobolevSpace.toLp μ Q v x)^(n+2)*H x ∂μ := by
    change κ*(a-(-(n+2:ℝ)*c-(n+1:ℝ)*a)) ≤ _ at hsource
    nlinarith only [hsource]
  have hcomp : a-b ≤ 2*(a+c) := power_energy_comparison μ Q u v A B hu hv hu0
    (hv0.mono fun _ hx => hx.le) n
  rw [power_source_energy_rate μ Q u v d e hd he A B hu hv n]
  change κ/2*(n+2:ℝ)*((n+1:ℝ)*(a-b)) ≤ _
  calc
    _ = (κ/2*(n+2:ℝ)*(n+1:ℝ))*(a-b) := by ring
    _ ≤ (κ/2*(n+2:ℝ)*(n+1:ℝ))*(2*(a+c)) :=
      mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ = (n+1:ℝ)*(κ*(n+2:ℝ)*(a+c)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)

end RegularPointCoordinates

end

end OAI
