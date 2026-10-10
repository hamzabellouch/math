import Mathlib
import OAI.Geometry.IntegralFillings.Charts.RectifiableMass
import OAI.Geometry.IntegralFillings.Currents.DisjointUnions
import OAI.Geometry.IntegralFillings.Charts.OverlapSum
import OAI.Geometry.IntegralFillings.Charts.ImageRestriction

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

namespace SharpIntegralFillings
open Set MeasureTheory Filter BorelCoefficients BorelRestriction MassMeasure
open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {k : ℕ}
lemma restrictCurrent_sum {T : Functional X k} {S : ℕ → Functional X k}
    (hT : IsMetricCurrent T) (hS : ∀ i, IsMetricCurrent (S i))
    (hsum : Summable (fun i => mass (S i)))
    (heq : ∀ b π, T b π = ∑' i, S i b π) {E : Set X} (hE : MeasurableSet E)
    (b : X → ℝ) (π : Fin k → X → ℝ) :
    restrictCurrent hT E b π = ∑' i, restrictCurrent (hS i) E b π := by
  let μ (i) := currentMassMeasure (hS i)
  have hμfin : ∀ i, IsFiniteMeasure (μ i) := fun i => inferInstance
  let := hμfin
  have hμsum : Summable (fun i => (μ i).real univ) := by
    simpa only [μ,currentMassMeasure_total] using hsum
  let := finite_sum_measure_of_summable_total μ hμsum
  have hμ (i) : Controls (S i) (μ i) := currentMassMeasure_controls (hS i)
  by_cases hab : Admissible b π
  · rw [restrictCurrent_apply hT E hab,
      borelAction_independent (currentMassMeasure hT) hT
        (currentMassMeasure_controls hT) (controls_sum hμ heq)
        ((integrable_boundedLip _ hab.1).indicator hE)
        ((integrable_boundedLip _ hab.1).indicator hE) π hab.2,
      borelAction_sum μ hT hS hμ heq
        ((integrable_boundedLip _ hab.1).indicator hE) π hab.2]
    exact tsum_congr fun i => (restrictCurrent_apply (hS i) E hab).symm
  · rw [(restrictCurrent_isMetricCurrent hT hE).offDomain b π hab]
    symm
    calc (∑' i, restrictCurrent (hS i) E b π) = ∑' (_i : ℕ), (0 : ℝ) :=
            tsum_congr fun i => (restrictCurrent_isMetricCurrent (hS i) hE).offDomain b π hab
      _ = 0 := tsum_zero

theorem integerRectifiable_chartSum [Nonempty X] (C : ℕ → IntegerChart X k)
    (hC : ∀ i, IsMetricCurrent (C i).action)
    (hsum : Summable (fun i => mass (C i).action)) :
    IntegerRectifiable (fun b π => ∑' i, (C i).action b π) := by
  let T : Functional X k := fun b π => ∑' i, (C i).action b π
  have hT : IsMetricCurrent T := isMetricCurrent_tsum hC hsum
  let Z : ℕ → Set X := disjointed (fun i => (C i).image)
  have hZ i : MeasurableSet (Z i) := MeasurableSet.disjointed (fun i => (C i).measurableSet_image) i
  have hd : Pairwise (fun i j => Disjoint (Z i) (Z j)) := disjoint_disjointed _
  have hZi i : Z i ⊆ (C i).image := disjointed_subset _ i
  have hZunion : (⋃ i, Z i) = ⋃ i, (C i).image := iUnion_disjointed
  let D i := (C i).restrictImage (Z i) (hZ i)
  have hDim i : (D i).image = Z i := by
    rw [IntegerChart.restrictImage_image,inter_eq_right.mpr (hZi i)]
  let F i j := (C j).restrictImage (Z i) (hZ i)
  have hF i j : IsMetricCurrent (F i j).action := (C j).restrictImage_isMetricCurrent _ _ (hC j)
  have hFS i : Summable (fun j => mass (F i j).action) :=
    hsum.of_nonneg_of_le (fun j => mass_nonneg _) (fun j => (C j).restrictImage_mass_le _ _ (hC j))
  have hFD i j : (F i j).image ⊆ (D i).image := by
    rw [hDim,IntegerChart.restrictImage_image]
    exact inter_subset_right
  choose E hEim hEact using fun i => IntegerChart.exists_overlap_sum (D i) (F i) (hFD i) (hF i) (hFS i)
  have hEeq i : (E i).action = restrictCurrent hT (Z i) := by
    funext b π
    rw [hEact,restrictCurrent_sum hT hC hsum (fun _ _ => rfl) (hZ i)]
    apply tsum_congr
    intro j
    exact congrFun (congrFun ((C j).restrictImage_action _ _ (hC j)) b) π
  have hEcurrent i : IsMetricCurrent (E i).action := by
    rw [hEeq]
    exact restrictCurrent_isMetricCurrent hT (hZ i)
  refine ⟨E,?_,hEcurrent,?_,?_⟩
  · intro i j hij
    simpa only [hEim,hDim] using hd hij
  · simp_rw [hEeq]
    exact summable_restriction_mass hT Z hZ hd
  · intro b π
    simp_rw [hEeq]
    rw [←restrictCurrent_iUnion hT Z hZ hd,hZunion,
      restrictCurrent_sum hT hC hsum (fun _ _ => rfl)
        (MeasurableSet.iUnion fun i => (C i).measurableSet_image)]
    apply tsum_congr
    intro i
    rw [(C i).restrictCurrent_image_eq (hC i)
      (MeasurableSet.iUnion fun i => (C i).measurableSet_image) (subset_iUnion (fun i => (C i).image) i)]

end SharpIntegralFillings

namespace SharpIntegralFillings
open Set MeasureTheory Filter BorelRestriction MassMeasure
open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ}

lemma IntegerChart.restrictCurrent_disjoint_eq_zero (C : IntegerChart X k)
    (hC : IsMetricCurrent C.action) {E : Set X} (hE : MeasurableSet E)
    (hd : Disjoint C.image E) : restrictCurrent hC E = 0 := by
  classical
  rw [←C.restrictMultiplicity_action hC hE]
  funext b π
  by_cases hab : Admissible b π
  · simp only [IntegerChart.action,ite_eq_left hab,Pi.zero_apply]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem C.borel] with z hz
    change z ∈ C.domain at hz
    have hi : C.paramExtended z ∉ E := by
      apply Set.disjoint_left.mp hd
      exact ⟨⟨z,hz⟩,by simp only [IntegerChart.paramExtended,dite_eq_left hz]⟩
    change ↑((C.paramExtended ⁻¹' E).indicator C.multiplicity z) * C.scalar b z * C.jacobian π z = 0
    rw [indicator_of_notMem (show z ∉ C.paramExtended ⁻¹' E from hi),Int.cast_zero,zero_mul,zero_mul]
  · simp only [IntegerChart.action,ite_eq_right hab,Pi.zero_apply]

end SharpIntegralFillings
end

end OAI
