import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.WeakMass

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
open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
noncomputable def atomCurrent (a : ℤ) (x : X) : Functional X 0 :=
  fun b π => if Admissible b π then (a : ℝ)*b x else 0

omit [MeasurableSpace X] [BorelSpace X] in
lemma atomCurrent_apply (a : ℤ) (x : X) {b : X → ℝ} {π : Fin 0 → X → ℝ}
    (hb : BoundedLip b) : atomCurrent a x b π = (a : ℝ)*b x :=
  ite_eq_left ⟨hb,fun i => Fin.elim0 i⟩

lemma atomCurrent_controls (a : ℤ) (x : X) :
    Controls (atomCurrent a x) (ENNReal.ofReal |(a : ℝ)| • Measure.dirac x) := by
  intro b π hb _
  rw [atomCurrent_apply a x hb,integral_smul_measure,integral_dirac,
    ENNReal.toReal_ofReal (abs_nonneg _),smul_eq_mul,abs_mul]

omit [MetricSpace X] [BorelSpace X] in
lemma finite_atom_measure (a : ℤ) (x : X) :
    IsFiniteMeasure (ENNReal.ofReal |(a : ℝ)| • Measure.dirac x) := by
  constructor
  simp only [Measure.smul_apply,Measure.dirac_apply_of_mem (mem_univ x),smul_eq_mul,mul_one]
  exact ENNReal.ofReal_lt_top

lemma atomCurrent_isMetricCurrent (a : ℤ) (x : X) : IsMetricCurrent (atomCurrent a x) := by
  refine ⟨fun b π h => ite_eq_right h,?_,?_,?_,?_,?_⟩
  · intro b c π r s hb hc _
    rw [atomCurrent_apply a x ((hb.const_mul r).add (hc.const_mul s)),
      atomCurrent_apply a x hb,atomCurrent_apply a x hc]
    ring
  · intro b π i
    exact Fin.elim0 i
  · intro b π πs hb _ _
    simp_rw [atomCurrent_apply a x hb]
    exact tendsto_const_nhds
  · rintro b π _ ⟨i,_⟩
    exact Fin.elim0 i
  · exact ⟨ENNReal.ofReal |(a : ℝ)| • Measure.dirac x,finite_atom_measure a x,atomCurrent_controls a x⟩

lemma mass_atomCurrent [CompactSpace X] (a : ℤ) (x : X) :
    mass (atomCurrent a x) = |(a : ℝ)| := by
  apply le_antisymm
  · apply (mass_le_measure (finite_atom_measure a x) (atomCurrent_controls a x)).trans_eq
    simp only [Measure.real,Measure.smul_apply,Measure.dirac_apply_of_mem (mem_univ x),
      smul_eq_mul,mul_one,ENNReal.toReal_ofReal (abs_nonneg _)]
  · have h := (atomCurrent_isMetricCurrent a x).mass_bound_uniform
      (BoundedLip.const (X := X) 1) (π := fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (M := 1) (fun _ => by norm_num)
    simpa only [atomCurrent_apply a x (BoundedLip.const 1),mul_one,
      Finset.univ_eq_empty,Finset.prod_empty,one_mul] using h

omit [MeasurableSpace X] [BorelSpace X] in
lemma IntegerChart.zero_action (C : IntegerChart X 0) (h : (0 : Euc 0) ∈ C.domain) :
    C.action = atomCurrent (C.multiplicity 0) (C.param ⟨0,h⟩) := by
  funext b π
  by_cases hab : Admissible b π
  · rw [IntegerChart.action,ite_eq_left hab,atomCurrent,ite_eq_left hab,volume_euclideanSpace_eq_dirac,
      restrict_dirac,ite_eq_left h,integral_dirac]
    have hj : C.jacobian π 0 = 1 := Matrix.det_isEmpty
    rw [hj,mul_one]
    simp only [IntegerChart.scalar,dite_eq_left h]
  · simp only [IntegerChart.action,atomCurrent,ite_eq_right hab]

omit [MeasurableSpace X] [BorelSpace X] in
lemma IntegerChart.zero_action_eq_zero (C : IntegerChart X 0) (h : (0 : Euc 0) ∉ C.domain) :
    C.action = 0 := by
  have hd : C.domain = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact h ((Subsingleton.elim z 0) ▸ hz)
  funext b π
  simp only [IntegerChart.action,hd,Measure.restrict_empty,integral_zero_measure,ite_self,Pi.zero_apply]

omit [MeasurableSpace X] [BorelSpace X] in
lemma IntegerChart.zero_exists_atom [Nonempty X] (C : IntegerChart X 0) :
    ∃ a : ℤ, ∃ x : X, C.action = atomCurrent a x := by
  by_cases h : (0 : Euc 0) ∈ C.domain
  · exact ⟨C.multiplicity 0,C.param ⟨0,h⟩,C.zero_action h⟩
  · refine ⟨0,Classical.arbitrary X,?_⟩
    rw [C.zero_action_eq_zero h]
    funext b π
    simp only [atomCurrent,Int.cast_zero,zero_mul,ite_self,Pi.zero_apply]

end CAT0Fillings

end

end OAI
