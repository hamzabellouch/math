import OAI.Geometry.RCD.Sobolev.SobolevPositivePower

namespace OAI

/-! # Exact weak-source pairing against two positive powers -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem weakLaplacian_power_product_test (f u v : SobolevSpace μ Q) (d : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ Q f d) (A B : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q u x| ≤ A)
    (hv : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q v x| ≤ B) (n m : ℕ) :
    (∫ x, (SobolevSpace.toLp μ Q v x)^(m+1)*
      ((n+1:ℝ)*(SobolevSpace.toLp μ Q u x)^n*localGamma μ Q u f x) ∂μ)+
    (∫ x, (SobolevSpace.toLp μ Q u x)^(n+1)*
      ((m+1:ℝ)*(SobolevSpace.toLp μ Q v x)^m*localGamma μ Q v f x) ∂μ) =
    -(∫ x, (SobolevSpace.toLp μ Q v x)^(m+1)*
      (SobolevSpace.toLp μ Q u x)^(n+1)*d x ∂μ) := by
  obtain ⟨U,hU,hUb,hUΓ⟩ := exists_sobolev_positive_power μ Q u A hu n
  obtain ⟨V,hV,hVb,hVΓ⟩ := exists_sobolev_positive_power μ Q v B hv m
  have he := IsWeakLaplacian.weighted_product μ Q f U V d hd (A^(n+1)) (B^(m+1)) hUb hVb
  have h₁ : weightedGamma μ Q (SobolevSpace.toLp μ Q V) f U =
      ∫ x, (SobolevSpace.toLp μ Q v x)^(m+1)*
        ((n+1:ℝ)*(SobolevSpace.toLp μ Q u x)^n*localGamma μ Q u f x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hV,hUΓ f,localGamma_comm μ Q f U] with x hx hy hz
    rw [hx,hz,hy]
  have h₂ : weightedGamma μ Q (SobolevSpace.toLp μ Q U) f V =
      ∫ x, (SobolevSpace.toLp μ Q u x)^(n+1)*
        ((m+1:ℝ)*(SobolevSpace.toLp μ Q v x)^m*localGamma μ Q v f x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hU,hVΓ f,localGamma_comm μ Q f V] with x hx hy hz
    rw [hx,hz,hy]
  have h₃ : (∫ x, SobolevSpace.toLp μ Q V x*SobolevSpace.toLp μ Q U x*d x ∂μ) =
      ∫ x, (SobolevSpace.toLp μ Q v x)^(m+1)*(SobolevSpace.toLp μ Q u x)^(n+1)*d x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hU,hV] with x hx hy
    rw [hx,hy]
  rwa [h₁,h₂,h₃] at he

end RegularPointCoordinates

end

end OAI
