import OAI.Geometry.RCD.Metric.FiniteDensityMeasure
import OAI.Geometry.RCD.Sobolev.LocalBochnerInput

namespace OAI

/-! # Actual localized Sobolev energy as a finite positive measure -/

open Set MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

def localEnergyMeasure (w : SobolevSpace μ hQ) (A : Set X) (c : ℝ) : FiniteMeasure X :=
  finiteDensityMeasure (μ.restrict A) ((localGamma_memL1 μ hQ w w).restrict.const_mul c)

theorem localEnergyMeasure_mass (w : SobolevSpace μ hQ) (A : Set X)
    {c : ℝ} (hc : 0≤c) :
    ((localEnergyMeasure μ hQ w A c).mass : ℝ)=c*∫ x in A, localGamma μ hQ w w x ∂μ := by
  rw [localEnergyMeasure,finiteDensityMeasure_mass,integral_const_mul]
  filter_upwards [ae_restrict_of_ae (localGamma_self μ hQ w)] with x hx
  exact mul_nonneg hc (hx ▸ sq_nonneg _)

theorem localEnergyMeasure_apply (w : SobolevSpace μ hQ) (A : Set X)
    {c : ℝ} (hc : 0≤c) {B : Set X} (hB : MeasurableSet B) :
    (localEnergyMeasure μ hQ w A c : Measure X).real B=
      c*∫ x in B, localGamma μ hQ w w x ∂μ.restrict A := by
  rw [localEnergyMeasure,finiteDensityMeasure_apply _ _ _ hB,integral_const_mul]
  filter_upwards [ae_restrict_of_ae (localGamma_self μ hQ w)] with x hx
  exact mul_nonneg hc (hx ▸ sq_nonneg _)

theorem localEnergyMeasure_le (w : SobolevSpace μ hQ) (A : Set X) (c C : ℝ)
    (hbound : ∀ᵐ x ∂μ.restrict A, c*localGamma μ hQ w w x≤C) :
    (localEnergyMeasure μ hQ w A c : Measure X)≤ENNReal.ofReal C • μ.restrict A := by
  change (μ.restrict A).withDensity _≤_
  rw [← withDensity_const]
  exact withDensity_mono (hbound.mono fun _ hx => ENNReal.ofReal_le_ofReal hx)

theorem localEnergyMeasure_absolutelyContinuous (w : SobolevSpace μ hQ) (A : Set X) (c : ℝ) :
    (localEnergyMeasure μ hQ w A c : Measure X) ≪ μ.restrict A :=
  withDensity_absolutelyContinuous _ _

end RegularPointCoordinates

end

end OAI
