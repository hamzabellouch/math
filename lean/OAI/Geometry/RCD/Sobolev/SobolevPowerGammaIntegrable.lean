import OAI.Geometry.RCD.Sobolev.SobolevPositivePower

namespace OAI

/-! # Integrability of bounded power weights against Sobolev energies -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
theorem sobolev_power_gamma_integrable (u v f g : SobolevSpace μ Q) (A B : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q u x| ≤ A)
    (hv : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q v x| ≤ B) (n m : ℕ) :
    Integrable (fun x => (SobolevSpace.toLp μ Q u x)^n*
      (SobolevSpace.toLp μ Q v x)^m*localGamma μ Q f g x) μ := by
  apply (localGamma_memL1 μ Q f g).bdd_mul (c := (A:ℝ)^n*(B:ℝ)^m)
    (((Lp.aestronglyMeasurable _).pow n).mul ((Lp.aestronglyMeasurable _).pow m))
  filter_upwards [hu,hv] with x hx hy
  change ‖(SobolevSpace.toLp μ Q u x)^n*(SobolevSpace.toLp μ Q v x)^m‖ ≤ _
  simp only [Real.norm_eq_abs,abs_mul,abs_pow]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hx n)
    (pow_le_pow_left₀ (abs_nonneg _) hy m) (pow_nonneg (abs_nonneg _) m)
    (pow_nonneg A.coe_nonneg n)

end RegularPointCoordinates

end

end OAI
