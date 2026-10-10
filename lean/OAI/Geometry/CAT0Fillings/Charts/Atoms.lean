import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.Atoms

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal
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

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
noncomputable def atomChart (a : ℤ) (x : X) : IntegerChart X 0 where
  domain := univ
  borel := MeasurableSet.univ
  bounded := Set.finite_univ.isCompact.isBounded
  param := fun _ => x
  bilipschitz := ⟨0,0,LipschitzWith.const x,AntilipschitzWith.of_subsingleton⟩
  multiplicity := fun _ => a
  integrable := by
    rw [Measure.restrict_univ,volume_euclideanSpace_eq_dirac]
    exact integrable_const _

omit [MeasurableSpace X] [BorelSpace X] in
lemma atomChart_action (a : ℤ) (x : X) : (atomChart a x).action = atomCurrent a x :=
  (atomChart a x).zero_action (mem_univ _)

lemma atomCurrent_integerRectifiable (a : ℤ) (x : X) : IntegerRectifiable (atomCurrent a x) := by
  classical
  let C : ℕ → IntegerChart X 0 := fun i => if i = 0 then atomChart a x else emptyChart 0
  have hC i : IsMetricCurrent (C i).action := by
    dsimp [C]
    split_ifs
    · rw [atomChart_action]; exact atomCurrent_isMetricCurrent a x
    · rw [emptyChart_action]; exact isMetricCurrent_zero 0
  have hzero i (hi : i ≠ 0) : (C i).action = 0 := by
    dsimp [C]
    rw [ite_eq_right hi,emptyChart_action]
    rfl
  refine ⟨C,?_,hC,?_,?_⟩
  · intro i j hij
    by_cases hi : i = 0
    · have hj : j ≠ 0 := by omega
      simp only [C,ite_eq_right hj,emptyChart_image,disjoint_empty]
    · simp only [C,ite_eq_right hi,emptyChart_image,empty_disjoint]
  · apply summable_of_ne_finset_zero (s := {0})
    intro i hi
    have hi' : i ≠ 0 := by simpa using hi
    rw [hzero i hi']
    exact mass_zero 0
  · intro b π
    rw [tsum_eq_single 0 (fun i hi => by rw [hzero i hi]; rfl)]
    simp only [C,ite_true,atomChart_action]

lemma atomCurrent_integral (a : ℤ) (x : X) : IsIntegral 0 (atomCurrent a x) :=
  ⟨atomCurrent_isMetricCurrent a x,atomCurrent_integerRectifiable a x⟩

end CAT0Fillings

end

end OAI
