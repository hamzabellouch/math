import Mathlib
import OAI.Geometry.CAT0Fillings.Model

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {k : ℕ}
omit [BorelSpace X] in
lemma controls_neg_iff {T : Functional X k} {μ : Measure X} :
    Controls (-T) μ ↔ Controls T μ := by
  simp only [Controls,Pi.neg_apply,abs_neg]

omit [BorelSpace X] in
lemma mass_neg (T : Functional X k) : mass (-T) = mass T := by
  simp only [mass,controls_neg_iff]

omit [BorelSpace X] in
lemma IsMetricCurrent.neg {T : Functional X k} (hT : IsMetricCurrent T) :
    IsMetricCurrent (-T) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro b π hab
    simp only [Pi.neg_apply,hT.offDomain b π hab,neg_zero]
  · intro b c π a d hb hc hπ
    simp only [Pi.neg_apply,hT.linearFirst b c π a d hb hc hπ]
    ring
  · intro b π i f a c hb hf
    simp only [Pi.neg_apply,hT.linearCoord b π i f a c hb hf]
    ring
  · intro b π πs hb hπ hlim
    exact (hT.sequentialContinuity b π πs hb hπ hlim).neg
  · intro b π hab hl
    simp only [Pi.neg_apply,hT.locality b π hab hl,neg_zero]
  · obtain ⟨μ,hμ,hc⟩ := hT.finiteMass
    exact ⟨μ,hμ,controls_neg_iff.mpr hc⟩

namespace IntegerChart
variable (C : IntegerChart X k)
noncomputable def negate : IntegerChart X k :=
  { C with multiplicity := fun z => -C.multiplicity z
           integrable := C.integrable.neg.congr (Eventually.of_forall fun _z => (Int.cast_neg _).symm) }

omit [MeasurableSpace X] [BorelSpace X] in
lemma negate_action : C.negate.action = -C.action := by
  classical
  funext b π
  by_cases hab : Admissible b π
  · simp only [action,ite_eq_left hab,Pi.neg_apply]
    change (∫ z in C.domain,(-C.multiplicity z:ℤ)*C.scalar b z*C.jacobian π z) =
      -(∫ z in C.domain,(C.multiplicity z:ℝ)*C.scalar b z*C.jacobian π z)
    simp only [Int.cast_neg,neg_mul,integral_neg]
  · simp only [action,ite_eq_right hab,Pi.neg_apply,neg_zero]
end IntegerChart

omit [BorelSpace X] in
lemma IntegerRectifiable.neg {T : Functional X k} (hI : IntegerRectifiable T) :
    IntegerRectifiable (-T) := by
  obtain ⟨C,hd,hC,hS,heq⟩ := hI
  refine ⟨fun i => (C i).negate,hd,?_,?_,?_⟩
  · intro i
    rw [IntegerChart.negate_action]
    exact (hC i).neg
  · simp_rw [IntegerChart.negate_action,mass_neg]
    exact hS
  · intro b π
    simp only [IntegerChart.negate_action,Pi.neg_apply,heq,tsum_neg]

end CAT0Fillings
end

end OAI
