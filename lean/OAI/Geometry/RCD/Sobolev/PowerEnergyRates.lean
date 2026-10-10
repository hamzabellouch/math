import OAI.Geometry.RCD.Sobolev.PowerSourceEnergyIdentity

namespace OAI

/-! # Normalized source rates for density powers -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem power_source_energy_rate (u v : SobolevSpace μ Q) (d e : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ Q u d) (he : IsWeakLaplacian μ Q v e) (A B : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q u x| ≤ A)
    (hv : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q v x| ≤ B) (n : ℕ) :
    (∫ x, (SobolevSpace.toLp μ Q u x*SobolevSpace.toLp μ Q v x)^(n+1)*
      (d x*SobolevSpace.toLp μ Q v x-SobolevSpace.toLp μ Q u x*e x) ∂μ) =
    (n+1:ℝ)*((∫ x, (SobolevSpace.toLp μ Q u x)^(n+2)*(SobolevSpace.toLp μ Q v x)^n*
      localGamma μ Q v v x ∂μ)-
      (∫ x, (SobolevSpace.toLp μ Q v x)^(n+2)*(SobolevSpace.toLp μ Q u x)^n*
        localGamma μ Q u u x ∂μ)) := by
  rw [power_source_energy_identity μ Q u v d e hd he A B hu hv n]
  have h₁ : (fun x => (SobolevSpace.toLp μ Q u x)^(n+2)*
      ((n+1:ℝ)*(SobolevSpace.toLp μ Q v x)^n*localGamma μ Q v v x)) =
      (fun x => (n+1:ℝ)*((SobolevSpace.toLp μ Q u x)^(n+2)*
        (SobolevSpace.toLp μ Q v x)^n*localGamma μ Q v v x)) := by funext x; ring
  have h₂ : (fun x => (SobolevSpace.toLp μ Q v x)^(n+2)*
      ((n+1:ℝ)*(SobolevSpace.toLp μ Q u x)^n*localGamma μ Q u u x)) =
      (fun x => (n+1:ℝ)*((SobolevSpace.toLp μ Q v x)^(n+2)*
        (SobolevSpace.toLp μ Q u x)^n*localGamma μ Q u u x)) := by funext x; ring
  rw [h₁,h₂,integral_const_mul,integral_const_mul]
  ring

theorem weakLaplacian_log_power_balance (u v : SobolevSpace μ Q) (e : Lp ℝ 2 μ)
    (he : IsWeakLaplacian μ Q v e) (A B : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q u x| ≤ A)
    (hv : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q v x| ≤ B) (n : ℕ) :
    (∫ x, (SobolevSpace.toLp μ Q v x)^(n+1)*(SobolevSpace.toLp μ Q u x)^(n+2)*e x ∂μ) =
    -(n+2:ℝ)*(∫ x, (SobolevSpace.toLp μ Q u x)^(n+1)*(SobolevSpace.toLp μ Q v x)^(n+1)*
      localGamma μ Q u v x ∂μ)-
    (n+1:ℝ)*(∫ x, (SobolevSpace.toLp μ Q u x)^(n+2)*(SobolevSpace.toLp μ Q v x)^n*
      localGamma μ Q v v x ∂μ) := by
  have hh := weakLaplacian_power_product_test μ Q v u v e he A B hu hv (n+1) n
  simp only [Nat.add_assoc,show (1:ℕ)+1 = 2 from rfl,Nat.cast_add,Nat.cast_one] at hh
  have h₁ : (fun x => (SobolevSpace.toLp μ Q v x)^(n+1)*
      (((n:ℝ)+1+1)*(SobolevSpace.toLp μ Q u x)^(n+1)*localGamma μ Q u v x)) =
      (fun x => (n+2:ℝ)*((SobolevSpace.toLp μ Q u x)^(n+1)*
        (SobolevSpace.toLp μ Q v x)^(n+1)*localGamma μ Q u v x)) := by funext x; ring
  have h₂ : (fun x => (SobolevSpace.toLp μ Q u x)^(n+2)*
      ((n+1:ℝ)*(SobolevSpace.toLp μ Q v x)^n*localGamma μ Q v v x)) =
      (fun x => (n+1:ℝ)*((SobolevSpace.toLp μ Q u x)^(n+2)*
        (SobolevSpace.toLp μ Q v x)^n*localGamma μ Q v v x)) := by funext x; ring
  rw [h₁,h₂,integral_const_mul,integral_const_mul] at hh
  linarith only [hh]

end RegularPointCoordinates

end

end OAI
