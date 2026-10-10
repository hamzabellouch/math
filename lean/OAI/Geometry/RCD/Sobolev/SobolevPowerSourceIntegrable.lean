import OAI.Geometry.RCD.Sobolev.SobolevPositivePower

namespace OAI

/-! # Integrability of bounded Sobolev power tests against L2 sources -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem sobolev_power_product_source_integrable (u v : SobolevSpace μ Q)
    (d : Lp ℝ 2 μ) (A B : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q u x| ≤ A)
    (hv : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q v x| ≤ B) (n m : ℕ) :
    Integrable (fun x => (SobolevSpace.toLp μ Q v x)^(m+1)*
      (SobolevSpace.toLp μ Q u x)^(n+1)*d x) μ := by
  obtain ⟨U,hU,hUb,_⟩ := exists_sobolev_positive_power μ Q u A hu n
  obtain ⟨V,hV,hVb,_⟩ := exists_sobolev_positive_power μ Q v B hv m
  let W := SobolevSpace.product μ Q U V (A^(n+1)) (B^(m+1))
  have hw := SobolevSpace.product_coe μ Q U V (A^(n+1)) (B^(m+1)) hUb hVb
  apply ((Lp.memLp (SobolevSpace.toLp μ Q W)).integrable_mul (Lp.memLp d)).congr
  filter_upwards [hw,hU,hV] with x hx hy hz
  change SobolevSpace.toLp μ Q (SobolevSpace.product μ Q U V (A^(n+1)) (B^(m+1))) x*d x = _
  rw [hx,hy,hz]
  ring

end RegularPointCoordinates

end

end OAI
