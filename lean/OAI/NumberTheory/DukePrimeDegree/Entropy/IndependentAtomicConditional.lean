import OAI.NumberTheory.DukePrimeDegree.Geometry.IndependentCoordinateKernel
import OAI.NumberTheory.DukePrimeDegree.Geometry.DiracFiberGraph

namespace OAI

/-! # Atomic root conditionals are unaffected by the neutral product factor -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree

variable {Z U V : Type*} [MeasurableSpace Z] [MeasurableSpace U] [MeasurableSpace V]
  [StandardBorelSpace U] [Nonempty U]

theorem atomic_conditional_of_independent_coordinate
    (ρ : Measure (Z × U)) [IsFiniteMeasure ρ]
    (η : Measure V) [IsProbabilityMeasure η]
    (h : ∀ᵐ z ∂independentCoordinateMeasure ρ η,
      (independentCoordinateMeasure ρ η).condKernel z.1=Measure.dirac z.2) :
    ∀ᵐ z ∂ρ, ρ.condKernel z.1=Measure.dirac z.2 := by
  have hc : ∀ᵐ z ∂independentCoordinateMeasure ρ η,
      (independentCoordinateMeasure ρ η).condKernel z.1=ρ.condKernel z.1.1 := by
    exact ae_of_ae_map measurable_fst.aemeasurable
      (independentCoordinateMeasure_condKernel ρ η)
  have he : ∀ᵐ z ∂independentCoordinateMeasure ρ η,
      ρ.condKernel z.1.1=Measure.dirac z.2 := by
    filter_upwards [h,hc] with z hz hc
    exact hc.symm.trans hz
  have hp : ∀ᵐ z ∂ρ.prod η, ρ.condKernel z.1.1=Measure.dirac z.1.2 := by
    exact exchangeLastCoordinates.measurableEmbedding.ae_map_iff.mp he
  filter_upwards [Measure.ae_ae_of_ae_prod hp] with z hz
  obtain ⟨v,hv⟩ := hz.exists
  exact hv

theorem independent_atomic_support_graph
    (ρ : Measure (Z × U)) [IsFiniteMeasure ρ]
    (η : Measure V) [IsProbabilityMeasure η]
    (h : ∀ᵐ z ∂independentCoordinateMeasure ρ η,
      (independentCoordinateMeasure ρ η).condKernel z.1=Measure.dirac z.2) :
    ∃ E : Set ((Z × U) × V), MeasurableSet E ∧ (∀ᵐ z ∂ρ.prod η, z ∈ E) ∧
      ∀ x ∈ E, ∀ y ∈ E, x.1.1=y.1.1 → x.1.2=y.1.2 := by
  obtain ⟨F,hF,hfull,hunique⟩ := exists_full_measure_unique_fiber_graph ρ ρ.condKernel
    (atomic_conditional_of_independent_coordinate ρ η h)
  refine ⟨Prod.fst ⁻¹' F,hF.preimage measurable_fst,?_,?_⟩
  · apply (Measure.ae_prod_iff_ae_ae (hF.preimage measurable_fst)).mpr
    filter_upwards [hfull] with z hz
    exact Filter.Eventually.of_forall fun _ => hz
  · intro x hx y hy he
    exact hunique x.1 hx y.1 hy he

end DukePrimeDegree

end

end OAI
