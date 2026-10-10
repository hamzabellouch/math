import OAI.Geometry.RCD.Heat.HeatPowerEnergyBalance
import OAI.Geometry.RCD.Sobolev.SobolevPowerSourceIntegrable

namespace OAI

/-! # The power-source rate equals the diagonal energy difference -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem power_source_energy_identity (u v : SobolevSpace μ Q) (d e : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ Q u d) (he : IsWeakLaplacian μ Q v e) (A B : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q u x| ≤ A)
    (hv : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q v x| ≤ B) (n : ℕ) :
    (∫ x, (SobolevSpace.toLp μ Q u x*SobolevSpace.toLp μ Q v x)^(n+1)*
      (d x*SobolevSpace.toLp μ Q v x-SobolevSpace.toLp μ Q u x*e x) ∂μ) =
    (∫ x, (SobolevSpace.toLp μ Q u x)^(n+2)*
      ((n+1:ℝ)*(SobolevSpace.toLp μ Q v x)^n*localGamma μ Q v v x) ∂μ)-
    (∫ x, (SobolevSpace.toLp μ Q v x)^(n+2)*
      ((n+1:ℝ)*(SobolevSpace.toLp μ Q u x)^n*localGamma μ Q u u x) ∂μ) := by
  have hdint := sobolev_power_product_source_integrable μ Q u v d A B hu hv n (n+1)
  have heint := sobolev_power_product_source_integrable μ Q u v e A B hu hv (n+1) n
  simp only [Nat.add_assoc,show (1:ℕ)+1 = 2 from rfl] at hdint heint
  have heq : (fun x => (SobolevSpace.toLp μ Q u x*SobolevSpace.toLp μ Q v x)^(n+1)*
      (d x*SobolevSpace.toLp μ Q v x-SobolevSpace.toLp μ Q u x*e x)) =
      (fun x => (SobolevSpace.toLp μ Q v x)^(n+2)*(SobolevSpace.toLp μ Q u x)^(n+1)*d x-
        (SobolevSpace.toLp μ Q v x)^(n+1)*(SobolevSpace.toLp μ Q u x)^(n+2)*e x) := by
    funext x
    rw [mul_pow,show n+2 = (n+1)+1 from rfl,pow_succ,pow_succ]
    ring
  rw [heq,integral_sub hdint heint]
  exact weakLaplacian_power_energy_balance μ Q u v d e hd he A B hu hv n

end RegularPointCoordinates

end

end OAI
