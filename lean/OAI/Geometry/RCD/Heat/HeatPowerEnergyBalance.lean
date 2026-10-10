import OAI.Geometry.RCD.Sobolev.WeakLaplacianPowerProduct

namespace OAI

/-! # Cancellation of the mixed energy in a heat-bridge power

The two actual L2 sources are paired against bounded Sobolev powers.
The mixed Gamma terms cancel without any derivative of either source.
-/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem weakLaplacian_power_energy_balance (u v : SobolevSpace μ Q) (d e : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ Q u d) (he : IsWeakLaplacian μ Q v e) (A B : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q u x| ≤ A)
    (hv : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q v x| ≤ B) (n : ℕ) :
    (∫ x, (SobolevSpace.toLp μ Q v x)^(n+2)*(SobolevSpace.toLp μ Q u x)^(n+1)*d x ∂μ)-
    (∫ x, (SobolevSpace.toLp μ Q v x)^(n+1)*(SobolevSpace.toLp μ Q u x)^(n+2)*e x ∂μ) =
    (∫ x, (SobolevSpace.toLp μ Q u x)^(n+2)*
      ((n+1:ℝ)*(SobolevSpace.toLp μ Q v x)^n*localGamma μ Q v v x) ∂μ)-
    (∫ x, (SobolevSpace.toLp μ Q v x)^(n+2)*
      ((n+1:ℝ)*(SobolevSpace.toLp μ Q u x)^n*localGamma μ Q u u x) ∂μ) := by
  have h₁ := weakLaplacian_power_product_test μ Q u u v d hd A B hu hv n (n+1)
  have h₂ := weakLaplacian_power_product_test μ Q v u v e he A B hu hv (n+1) n
  have hcross :
      (∫ x, (SobolevSpace.toLp μ Q u x)^(n+1)*
        (((n+1:ℕ)+1:ℝ)*(SobolevSpace.toLp μ Q v x)^(n+1)*localGamma μ Q v u x) ∂μ) =
      (∫ x, (SobolevSpace.toLp μ Q v x)^(n+1)*
        (((n+1:ℕ)+1:ℝ)*(SobolevSpace.toLp μ Q u x)^(n+1)*localGamma μ Q u v x) ∂μ) := by
    apply integral_congr_ae
    filter_upwards [localGamma_comm μ Q v u] with x hx
    rw [hx]
    ring
  simp only [Nat.add_assoc,show (1:ℕ)+1 = 2 from rfl] at h₁ h₂
  rw [hcross] at h₁
  linarith only [h₁,h₂]

end RegularPointCoordinates

end

end OAI
