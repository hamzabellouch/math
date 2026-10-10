import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.Restriction
import OAI.Geometry.CAT0Fillings.Charts.DomainRestriction

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
open scoped Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)
noncomputable def restrictImage (E : Set X) (hE : MeasurableSet E) : IntegerChart X k :=
  C.restrictDomain (C.borel.inter (C.measurable_paramExtended hE)) inter_subset_left

omit [CompactSpace X] in
lemma restrictImage_image (E : Set X) (hE : MeasurableSet E) :
    (C.restrictImage E hE).image = C.image ∩ E := by
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨⟨⟨z,z.property.1⟩,rfl⟩,by
      change C.param ⟨z,z.property.1⟩ ∈ E
      simpa only [mem_preimage,paramExtended,dite_eq_left z.property.1] using z.property.2⟩
  · rintro ⟨⟨z,rfl⟩,hz⟩
    refine ⟨⟨z,⟨z.property,?_⟩⟩,rfl⟩
    simpa only [mem_preimage,paramExtended,dite_eq_left z.property] using hz

lemma restrictImage_action (E : Set X) (hE : MeasurableSet E)
    (hC : IsMetricCurrent C.action) :
    (C.restrictImage E hE).action = BorelRestriction.restrictCurrent hC E := by
  classical
  let t := C.domain ∩ C.paramExtended ⁻¹' E
  have ht : MeasurableSet t := C.borel.inter (C.measurable_paramExtended hE)
  have hts : t ⊆ C.domain := inter_subset_left
  have him : MeasurableSet (C.paramExtended '' t) := C.measurableSet_paramExtended_image ht hts
  change (C.restrictDomain ht hts).action = _
  rw [C.restrictDomain_action ht hts hC,←C.restrictMultiplicity_action hC him,
    ←C.restrictMultiplicity_action hC hE]
  funext b π
  by_cases hab : Admissible b π
  · simp only [action,ite_eq_left hab]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem C.borel] with z hz
    have hi : C.paramExtended z ∈ C.paramExtended '' t ↔ C.paramExtended z ∈ E := by
      rw [C.paramExtended_mem_image_iff hts hz]
      exact and_iff_right hz
    change (↑((C.paramExtended ⁻¹' (C.paramExtended '' t)).indicator C.multiplicity z) : ℝ) *
      C.scalar b z * C.jacobian π z =
      ↑((C.paramExtended ⁻¹' E).indicator C.multiplicity z) * C.scalar b z * C.jacobian π z
    by_cases he : C.paramExtended z ∈ E
    · rw [indicator_of_mem (show z ∈ C.paramExtended ⁻¹' (C.paramExtended '' t) from hi.mpr he),
        indicator_of_mem (show z ∈ C.paramExtended ⁻¹' E from he)]
    · rw [indicator_of_notMem (show z ∉ C.paramExtended ⁻¹' (C.paramExtended '' t) from mt hi.mp he),
        indicator_of_notMem (show z ∉ C.paramExtended ⁻¹' E from he)]
  · simp only [action,ite_eq_right hab]

lemma restrictImage_isMetricCurrent (E : Set X) (hE : MeasurableSet E)
    (hC : IsMetricCurrent C.action) : IsMetricCurrent (C.restrictImage E hE).action := by
  rw [C.restrictImage_action E hE hC]
  exact BorelRestriction.restrictCurrent_isMetricCurrent hC hE

lemma restrictImage_mass_le (E : Set X) (hE : MeasurableSet E)
    (hC : IsMetricCurrent C.action) : mass (C.restrictImage E hE).action ≤ mass C.action := by
  rw [C.restrictImage_action E hE hC,BorelRestriction.restriction_mass hC hE,
    ←MassMeasure.currentMassMeasure_total hC]
  exact measureReal_mono (subset_univ E)

lemma restrictCurrent_image_eq (hC : IsMetricCurrent C.action) {E : Set X}
    (hE : MeasurableSet E) (hCE : C.image ⊆ E) :
    BorelRestriction.restrictCurrent hC E = C.action := by
  classical
  rw [←C.restrictMultiplicity_action hC hE]
  funext b π
  by_cases hab : Admissible b π
  · simp only [action,ite_eq_left hab]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem C.borel] with z hz
    change z ∈ C.domain at hz
    have hi : C.paramExtended z ∈ E := hCE ⟨⟨z,hz⟩,by simp only [paramExtended,dite_eq_left hz]⟩
    change (↑((C.paramExtended ⁻¹' E).indicator C.multiplicity z) : ℝ) *
      C.scalar b z * C.jacobian π z = _
    rw [indicator_of_mem (show z ∈ C.paramExtended ⁻¹' E from hi)]
  · simp only [action,ite_eq_right hab]

end IntegerChart
end CAT0Fillings

end

end OAI
