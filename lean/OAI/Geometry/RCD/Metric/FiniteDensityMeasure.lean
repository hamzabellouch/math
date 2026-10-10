import OAI.Geometry.RCD.Coordinates.NormalizedDensityLaw
import OAI.Geometry.RCD.Metric.EuclideanFiniteMeasureCompactness

namespace OAI

/-! # Finite nonnegative density measures without mass normalization -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

def finiteDensityMeasure (μ : Measure X) {f : X → ℝ} (hi : Integrable f μ) :
    FiniteMeasure X :=
  ⟨μ.withDensity (fun x => ENNReal.ofReal (f x)), isFiniteMeasure_withDensity_ofReal hi.2⟩

theorem finiteDensityMeasure_mass (μ : Measure X) {f : X → ℝ}
    (hi : Integrable f μ) (hn : 0≤ᵐ[μ] f) :
    ((finiteDensityMeasure μ hi).mass : ℝ)=∫ x, f x ∂μ := by
  change (μ.withDensity (fun x => ENNReal.ofReal (f x)) univ).toReal=_
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    integral_eq_lintegral_of_nonneg_ae hn hi.aestronglyMeasurable]

theorem finiteDensityMeasure_apply (μ : Measure X) {f : X → ℝ}
    (hi : Integrable f μ) (hn : 0≤ᵐ[μ] f) {A : Set X} (hA : MeasurableSet A) :
    (finiteDensityMeasure μ hi : Measure X).real A=∫ x in A, f x ∂μ := by
  change (μ.withDensity (fun x => ENNReal.ofReal (f x)) A).toReal=_
  rw [withDensity_apply _ hA,
    integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hn) hi.restrict.aestronglyMeasurable]

theorem finiteDensityMeasure_integral (μ : Measure X) {f : X → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) (hn : 0≤ᵐ[μ] f) (g : X → ℝ) :
    (∫ x, g x ∂(finiteDensityMeasure μ hi : Measure X))=∫ x, f x*g x ∂μ := by
  change (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x)))=_
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  exact integral_congr_ae (hn.mono fun x hx => by simp [ENNReal.toReal_ofReal hx])

end RegularPointCoordinates

end

end OAI
