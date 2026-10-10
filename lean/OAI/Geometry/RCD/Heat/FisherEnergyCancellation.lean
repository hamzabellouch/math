import OAI.Geometry.RCD.Sobolev.WeakLaplacianWeightedProduct

namespace OAI

/-! # The bounded product cancellation in Fisher variation -/

open MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem fisher_energy_product_swap (u w H : SobolevSpace μ hQ) (ε : ℝ)
    (A C B : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x|≤A)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x|≤C)
    (hH : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ H x|≤B) :
    energyForm μ hQ H (ε • w+SobolevSpace.product μ hQ u w A C)-
      energyForm μ hQ w (ε • H+SobolevSpace.product μ hQ u H A B) =
      weightedGamma μ hQ (SobolevSpace.toLp μ hQ w) u H-
        weightedGamma μ hQ (SobolevSpace.toLp μ hQ H) u w := by
  simp only [energyForm_add_right,energyForm_smul_right]
  rw [energyForm_comm μ hQ H (SobolevSpace.product μ hQ u w A C),
    energyForm_product_test μ hQ u w H A C hu hw,
    energyForm_comm μ hQ w (SobolevSpace.product μ hQ u H A B),
    energyForm_product_test μ hQ u H w A B hu hH,
    energyForm_comm μ hQ H w,
    weightedGamma_comm μ hQ (SobolevSpace.toLp μ hQ u) w H]
  ring

theorem fisher_energy_source_cancellation (u w H : SobolevSpace μ hQ)
    (d : Lp ℝ 2 μ) (hd : IsWeakLaplacian μ hQ u d) (ε : ℝ) (A C B : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x|≤A)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x|≤C)
    (hH : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ H x|≤B) :
    energyForm μ hQ H (ε • w+SobolevSpace.product μ hQ u w A C)-
      energyForm μ hQ w (ε • H+SobolevSpace.product μ hQ u H A B)+
      (∫ x, SobolevSpace.toLp μ hQ w x*SobolevSpace.toLp μ hQ H x*d x ∂μ)+
      2*weightedGamma μ hQ (SobolevSpace.toLp μ hQ H) u w = 0 := by
  rw [fisher_energy_product_swap μ hQ u w H ε A C B hu hw hH]
  have ht := IsWeakLaplacian.weighted_product μ hQ u H w d hd B C hH hw
  linarith only [ht]

end RegularPointCoordinates

end

end OAI
