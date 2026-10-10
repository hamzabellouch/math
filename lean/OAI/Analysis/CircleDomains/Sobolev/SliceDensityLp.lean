import OAI.Analysis.CircleDomains.Probability.SphericalSliceDensity
import OAI.Analysis.CircleDomains.Sobolev.DensityL2
import OAI.Analysis.CircleDomains.Topology.EuclideanPlaneCoordinates

namespace OAI

/-! The finite-chart slice density has finite L² norm in complex,
Cartesian and Euclidean coordinates. -/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem sliceChartDensity_complex_memLp
    (B : ℝ≥0) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) :
    MemLp (fun z : ℂ => (sliceChartDensity B g z).toReal) 2 volume :=
  memLp_two_toReal_of_lintegral_sq_ne_top volume
    (measurable_sliceChartDensity B hg) (sliceChartDensity_sq_integral_finite B g hg henergy).ne

 theorem sliceChartDensity_realProd_memLp
    (B : ℝ≥0) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) :
    MemLp (fun p : ℝ × ℝ => (sliceChartDensity B g ⟨p.1, p.2⟩).toReal) 2 volume :=
  (sliceChartDensity_complex_memLp B g hg henergy).comp_measurePreserving
    (Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd)

 theorem sliceChartDensity_euclidean_memLp
    (B : ℝ≥0) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) :
    MemLp (fun p : EuclideanPlane => (sliceChartDensity B g ⟨p 0, p 1⟩).toReal) 2 volume := by
  have heq : (fun p : EuclideanPlane => (sliceChartDensity B g ⟨p 0, p 1⟩).toReal) =
      (fun p : ℝ × ℝ => (sliceChartDensity B g ⟨p.1, p.2⟩).toReal) ∘
        euclideanPlaneCoordinates := by
    funext p
    rfl
  rw [heq]
  exact (sliceChartDensity_realProd_memLp B g hg henergy).comp_measurePreserving
    euclideanPlaneCoordinates_measurePreserving

end CircleDomainRigidity

end

end OAI
