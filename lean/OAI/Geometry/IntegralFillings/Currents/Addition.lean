import Mathlib
import OAI.Geometry.IntegralFillings.Slicing.RectifiableCoarea

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

namespace SharpIntegralFillings
open Set MeasureTheory Filter MassMeasure BorelCoefficients
open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {k : ℕ}
lemma controls_add {T U : Functional X k} {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hT : Controls T μ) (hU : Controls U ν) :
    Controls (T+U) (μ+ν) := by
  intro b π hb hπ
  have hiμ := (integrable_boundedLip μ hb).abs
  have hiν := (integrable_boundedLip ν hb).abs
  change |T b π + U b π| ≤ _
  rw [integral_add_measure hiμ hiν]
  exact (abs_add_le _ _).trans (add_le_add (hT b π hb hπ) (hU b π hb hπ))

lemma IsMetricCurrent.add {T U : Functional X k} (hT : IsMetricCurrent T)
    (hU : IsMetricCurrent U) : IsMetricCurrent (T+U) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro b π hab
    simp only [Pi.add_apply,hT.offDomain b π hab,hU.offDomain b π hab,add_zero]
  · intro b c π a d hb hc hπ
    simp only [Pi.add_apply,hT.linearFirst b c π a d hb hc hπ,
      hU.linearFirst b c π a d hb hc hπ]
    ring
  · intro b π i f a c hb hf
    simp only [Pi.add_apply,hT.linearCoord b π i f a c hb hf,
      hU.linearCoord b π i f a c hb hf]
    ring
  · intro b π πs hb hπ hlim
    exact (hT.sequentialContinuity b π πs hb hπ hlim).add
      (hU.sequentialContinuity b π πs hb hπ hlim)
  · intro b π hab hl
    simp only [Pi.add_apply,hT.locality b π hab hl,hU.locality b π hab hl,add_zero]
  · obtain ⟨μ,hμ,hc⟩ := hT.finiteMass
    obtain ⟨ν,hν,hd⟩ := hU.finiteMass
    let := hμ; let := hν
    exact ⟨μ+ν,inferInstance,controls_add hc hd⟩

lemma mass_add_le {T U : Functional X k} (hT : IsMetricCurrent T)
    (hU : IsMetricCurrent U) : mass (T+U) ≤ mass T + mass U := by
  have hh := mass_le_measure (μ := currentMassMeasure hT + currentMassMeasure hU)
    inferInstance (controls_add (currentMassMeasure_controls hT) (currentMassMeasure_controls hU))
  have he : (currentMassMeasure hT + currentMassMeasure hU).real univ =
      (currentMassMeasure hT).real univ + (currentMassMeasure hU).real univ := by
    simp only [Measure.real,Measure.add_apply,ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  rw [he,currentMassMeasure_total,currentMassMeasure_total] at hh
  exact hh

lemma IntegerRectifiable.add [Nonempty X] {T U : Functional X k}
    (hT : IsMetricCurrent T) (hU : IsMetricCurrent U)
    (hI : IntegerRectifiable T) (hJ : IntegerRectifiable U) : IntegerRectifiable (T+U) := by
  let A : ℕ → Functional X k := fun i => if i=0 then T else if i=1 then U else 0
  have hA i : IsMetricCurrent (A i) := by
    dsimp [A]; split_ifs <;> first | exact hT | exact hU | exact isMetricCurrent_zero _
  have hAI i : IntegerRectifiable (A i) := by
    dsimp [A]; split_ifs <;> first | exact hI | exact hJ | exact integerRectifiable_zero _
  have hAS : Summable (fun i => mass (A i)) := by
    apply summable_of_ne_finset_zero (s := {0,1})
    intro i hi
    have h0 : i ≠ 0 := fun h => hi (by simp [h])
    have h1 : i ≠ 1 := fun h => hi (by simp [h])
    simp only [A,ite_eq_right h0,ite_eq_right h1]
    exact mass_zero _
  have heq : (fun b π => ∑' i, A i b π) = T+U := by
    funext b π
    rw [tsum_eq_sum (s := {0,1}) (fun i hi => ?_)]
    · simp [A]
    · have h0 : i ≠ 0 := fun h => hi (by simp [h])
      have h1 : i ≠ 1 := fun h => hi (by simp [h])
      simp [A,h0,h1]
  rw [←heq]
  exact integerRectifiable_tsum hA hAI hAS

end SharpIntegralFillings
end

end OAI
