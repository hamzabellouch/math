import OAI.Geometry.RCD.Sobolev.DistancePoissonMeanData
import OAI.Geometry.RCD.Coordinates.RegularCoreRepresentative

namespace OAI

/-! # Fixed representatives for the simultaneous compact Poisson extensions -/

open Set Filter Metric MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates.DistancePoissonMeanData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {Q : QuadraticCheegerEnergy μ}
  {n : ℕ} {κ B J C : ℝ} {p : ℕ → X} {r : ℕ → ℝ} {hr : ∀ k, 0<r k}
  {F : DistancePoissonFamily μ Q n κ B J C p r hr} (D : DistancePoissonMeanData F)

def representative (k : ℕ) : X → ℝ :=
  Classical.choose (regular_core_representative μ Q (D.extension k))

theorem representative_spec (k : ℕ) : ∃ L A : ℝ≥0,
    LipschitzWith L (D.representative k) ∧ HasCompactSupport (D.representative k) ∧
    (SobolevSpace.toLp μ Q (D.extension k).val =ᵐ[μ] D.representative k) ∧
    ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q (D.extension k).val x|≤A :=
  Classical.choose_spec (regular_core_representative μ Q (D.extension k))

theorem representative_local_eq (k : ℕ) : D.representative k
    =ᵐ[μ.restrict (ball (p k) (r k/16))] SobolevSpace.toLp μ Q (F.replacement k) := by
  obtain ⟨L,A,hL,hc,he,hA⟩ := D.representative_spec k
  filter_upwards [ae_restrict_of_ae he,D.replacement_eq k] with x hx hy
  exact hx.symm.trans hy

end RegularPointCoordinates.DistancePoissonMeanData

end

end OAI
