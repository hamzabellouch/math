import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.ExactMass
import OAI.Geometry.CAT0Fillings.Currents.CanonicalMass
import OAI.Geometry.CAT0Fillings.Currents.ComponentMass

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)
lemma measurableSet_image : MeasurableSet C.image := by
  have heq : C.image = C.paramExtended '' C.domain := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨z,z.property,by simp only [paramExtended,dite_eq_left z.property]⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z,hz⟩,by simp only [paramExtended,dite_eq_left hz]⟩
  rw [heq]
  exact C.measurableSet_paramExtended_image C.borel (Subset.rfl)

lemma majorantMeasure_ae_image (J : Euc k → ℝ) :
    ∀ᵐ x ∂C.majorantMeasure J, x ∈ C.image := by
  rw [majorantMeasure,densityPush]
  apply (ae_map_iff C.measurable_paramExtended.aemeasurable C.measurableSet_image).mpr
  have hmem := (withDensity_absolutelyContinuous (volume.restrict C.domain)
    (fun z => ENNReal.ofReal (|(C.multiplicity z : ℝ)| * J z))).ae_le (ae_restrict_mem C.borel)
  filter_upwards [hmem] with z hz
  exact ⟨⟨z,hz⟩,by simp only [paramExtended,dite_eq_left hz]⟩

end IntegerChart

theorem integerRectifiable_exact_mass
    {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    {k : ℕ} {T : Functional X k} (hX : IsCAT0 X)
    (hT : IsMetricCurrent T) (hrect : IntegerRectifiable T) :
    ∃ (C : ℕ → IntegerChart X k) (P : ℕ → Euc k → Matrix (Fin k) (Fin k) ℝ),
      Pairwise (fun i j => Disjoint (C i).image (C j).image) ∧
      (∀ b π, T b π = ∑' i, (C i).action b π) ∧
      (∀ i a b, Measurable (fun z => P i z a b)) ∧
      (∀ i, ∀ᵐ z ∂volume.restrict (C i).domain, (P i z).PosDef) ∧
      (∀ i, Integrable (fun z => |((C i).multiplicity z : ℝ)| * Real.sqrt (P i z).det)
        (volume.restrict (C i).domain)) ∧
      (∀ i, ∃ p : Euc k → Seminorm ℝ (Euc k),
        P i = (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis) ∧
        (∀ v, Measurable (fun z => p z v)) ∧
        ∀ᵐ z ∂volume.restrict (C i).domain,
          (∀ hz : z ∈ (C i).domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
            (C i).domain (C i).param (p z) ⟨z,hz⟩) ∧
          (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
          (∀ v, p z v = 0 ↔ v = 0)) ∧
      MassMeasure.currentMassMeasure hT =
        Measure.sum (fun i => (C i).majorantMeasure (fun z => Real.sqrt (P i z).det)) := by
  classical
  let C := hrect.choose
  have hdis := hrect.choose_spec.1
  have hC := hrect.choose_spec.2.1
  have hsum := hrect.choose_spec.2.2.1
  have heq := hrect.choose_spec.2.2.2
  choose P hPm hP hρ hfin hctrl hmin hfield using
    (fun i => (C i).exists_exact_quadratic_mass hX (hC i))
  let μ : ℕ → Measure X := fun i => (C i).majorantMeasure (fun z => Real.sqrt (P i z).det)
  have hμfin : ∀ i, IsFiniteMeasure (μ i) := hfin
  let := hμfin
  have hmass (i) : MassMeasure.currentMassMeasure (hC i) = μ i := by
    apply le_antisymm (MassMeasure.currentMassMeasure_le (hC i) (hctrl i))
    exact hmin i _ inferInstance (MassMeasure.currentMassMeasure_controls (hC i))
  have htot (i) : (μ i).real univ = mass (C i).action := by
    rw [←hmass i]
    exact MassMeasure.currentMassMeasure_total _
  have hμsum : Summable (fun i => (μ i).real univ) := by
    simpa only [htot] using hsum
  let := finite_sum_measure_of_summable_total μ hμsum
  refine ⟨C,P,hdis,heq,hPm,hP,hρ,hfield,?_⟩
  apply le_antisymm
  · exact MassMeasure.currentMassMeasure_le hT (controls_sum hctrl heq)
  · exact sum_measure_le_of_component_minimal hC hctrl hmin heq
      (fun i => (C i).measurableSet_image) hdis
      (fun i => (C i).majorantMeasure_ae_image _) (MassMeasure.currentMassMeasure_controls hT)

end CAT0Fillings

namespace CAT0Fillings
attribute [local instance] Classical.propDecidable
end CAT0Fillings
end

end OAI
