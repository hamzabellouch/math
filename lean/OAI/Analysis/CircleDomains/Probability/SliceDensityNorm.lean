import OAI.Analysis.CircleDomains.Sobolev.SliceDensityLp
import OAI.Analysis.CircleDomains.Topology.PhysicalPlaneCoordinates

namespace OAI

/-! The slice density used by the smoothed mean has a quantitative L²
bound in the same Euclidean chart as its partial derivatives. -/

open MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem eLpNorm_toReal_le_square_integral
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (g : X → ℝ≥0∞)
    (hmem : MemLp (fun x => (g x).toReal) 2 μ) :
    eLpNorm (fun x => (g x).toReal) 2 μ ≤ (∫⁻ x, g x ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hmem.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  apply lintegral_mono
  intro x
  apply pow_le_pow_left'
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

 theorem sliceChartDensity_complex_eLpNorm_le
    (B : ℝ≥0) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) :
    eLpNorm (fun z : ℂ => (sliceChartDensity B g z).toReal) 2 volume ≤
      (2 * (B : ℝ≥0∞)) * (∫⁻ p, g p ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ) := by
  apply (eLpNorm_toReal_le_square_integral volume (sliceChartDensity B g)
    (sliceChartDensity_complex_memLp B g hg henergy)).trans
  have h := ENNReal.rpow_le_rpow (sliceChartDensity_sq_integral_le B g hg)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at h
  have hconst : (4 * (B : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) = 2 * B := by
    rw [show (4 : ℝ≥0∞) * B ^ 2 = (2 * (B : ℝ≥0∞)) ^ 2 by ring,
      ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  rwa [hconst] at h

 theorem sliceChartDensity_euclidean_eLpNorm_le
    (B : ℝ≥0) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞)
    (Ω : Set EuclideanPlane) :
    eLpNorm (fun x : EuclideanPlane => (sliceChartDensity B g ⟨x 0, x 1⟩).toReal)
      2 (volume.restrict Ω) ≤
      (2 * (B : ℝ≥0∞)) * (∫⁻ p, g p ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ) := by
  have hmp : MeasurePreserving complexPlaneCoordinates volume volume :=
    (Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd).comp
      euclideanPlaneCoordinates_measurePreserving
  calc
    _ ≤ eLpNorm (fun x : EuclideanPlane => (sliceChartDensity B g ⟨x 0, x 1⟩).toReal)
        2 volume := eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = eLpNorm (fun z : ℂ => (sliceChartDensity B g z).toReal) 2 volume :=
      eLpNorm_comp_measurePreserving
        (sliceChartDensity_complex_memLp B g hg henergy).aestronglyMeasurable hmp
    _ ≤ _ := sliceChartDensity_complex_eLpNorm_le B g hg henergy

end CircleDomainRigidity

end

end OAI
