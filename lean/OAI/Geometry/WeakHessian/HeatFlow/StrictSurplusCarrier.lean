import Mathlib
import OAI.Geometry.WeakHessian.Measure.MeasurePositiveNegativeBalance

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian

section CarrierBounds
open MeasureTheory Set
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

lemma exists_ac_full_carrier (ν δ : Measure X) [IsFiniteMeasure ν] [IsFiniteMeasure δ] :
    ∃ P : Set X, MeasurableSet P ∧ δ Pᶜ = 0 ∧ ν.restrict P ≪ δ := by
  obtain ⟨P,hP,hsp,hδ⟩ := Measure.mutuallySingular_singularPart ν δ
  refine ⟨P,hP,hδ,?_⟩
  have he : ν.restrict P = (δ.withDensity (ν.rnDeriv δ)).restrict P := by
    conv_lhs => rw [Measure.haveLebesgueDecomposition_add ν δ]
    rw [Measure.restrict_add,Measure.restrict_eq_zero.mpr hsp,zero_add]
  rw [he]
  exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans
    (withDensity_absolutelyContinuous δ (ν.rnDeriv δ))

structure StrictSurplusCarrier (μ ν : Measure X) (P : Set X) : Prop where
  measurableSet : MeasurableSet P
  surplus_compl : (μ-ν) Pᶜ = 0
  reference_ac : ν.restrict P ≪ μ-ν
  deficit_zero : (ν-μ) P = 0

lemma exists_strictSurplusCarrier (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ∃ P : Set X, StrictSurplusCarrier μ ν P := by
  let : IsFiniteMeasure (μ-ν) := isFiniteMeasure_of_le μ Measure.sub_le
  obtain ⟨S,hS,hδ,hν⟩ := exists_ac_full_carrier ν (μ-ν)
  obtain ⟨T,hT,hTδ,hTκ⟩ := (Measure.mutually_singular_measure_sub (μ := μ) (ν := ν))
  refine ⟨S ∩ Tᶜ,⟨hS.inter hT.compl,?_,?_,?_⟩⟩
  · rw [compl_inter,compl_compl]
    apply measure_union_null hδ hTδ
  · exact (Measure.absolutelyContinuous_of_le (Measure.restrict_mono_set ν inter_subset_left)).trans hν
  · exact measure_mono_null inter_subset_right hTκ

variable [MetricSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
lemma StrictSurplusCarrier.mass_ac {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {P : Set X} (hP : StrictSurplusCarrier μ ν P) : μ.restrict P ≪ μ-ν := by
  have h := Measure.restrict_mono_measure (measure_le_sub_add μ ν) P
  rw [Measure.restrict_add] at h
  exact (Measure.absolutelyContinuous_of_le h).trans
    ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).add_left hP.reference_ac)

omit [MetricSpace X] [BorelSpace X] in
lemma StrictSurplusCarrier.reference_le_mass {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {P : Set X} (hP : StrictSurplusCarrier μ ν P) :
    ν P ≤ μ P := by
  have h := measure_le_sub_add ν μ P
  simpa only [Measure.add_apply,hP.deficit_zero,zero_add] using h

omit [MetricSpace X] [BorelSpace X] in
lemma StrictSurplusCarrier.surplus_le_mass {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {P : Set X} (hP : StrictSurplusCarrier μ ν P) :
    (μ-ν) univ ≤ μ P := by
  have H := Measure.sub_le (μ := μ) (ν := ν) P
  rw [← measure_add_measure_compl hP.measurableSet,hP.surplus_compl,add_zero]
  exact H

omit [MetricSpace X] [BorelSpace X] in
lemma StrictSurplusCarrier.maximal_reference_volume {μ ν : Measure X}
    {P : Set X} (hP : StrictSurplusCarrier μ ν P)
    {A : Set X} (hA : MeasurableSet A) (hνA : ν.restrict A ≪ μ-ν) : ν A ≤ ν P := by
  have hzero : ν (A ∩ Pᶜ) = 0 := by
    have hh := hνA hP.surplus_compl
    rw [Measure.restrict_apply hP.measurableSet.compl,inter_comm] at hh
    exact hh
  calc
    ν A = ν (A ∩ P) + ν (A ∩ Pᶜ) := by
      rw [← measure_union (disjoint_left.mpr (by aesop)) (hA.inter hP.measurableSet.compl)]
      congr 1
      ext x
      simp only [mem_union,mem_inter_iff,mem_compl_iff]
      tauto
    _ ≤ ν P := by rw [hzero,add_zero]; exact measure_mono inter_subset_right

end CarrierBounds
open MeasureTheory Set
open scoped ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
lemma StrictSurplusCarrier.exact_mass {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {P : Set X}
    (hP : StrictSurplusCarrier μ ν P) : μ P = ν P + (μ-ν) univ := by
  have H := congrArg (fun η : Measure X => η P) (measure_positive_negative_balance μ ν)
  simp only [Measure.add_apply,hP.deficit_zero,add_zero] at H
  rw [← measure_add_measure_compl hP.measurableSet,hP.surplus_compl,add_zero]
  exact H

omit [MetricSpace X] [BorelSpace X] in
lemma excess_relocation_carrier_growth (μ ν ρ β : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure β]
    {P : Set X} (_hP : StrictSurplusCarrier μ ν P)
    (hρ : ρ ≤ μ-ν) (hmass : β univ = ρ univ)
    (hmin : (μ-ν) univ ≤ ((μ-ρ+β)-ν) univ)
    (hspread : ∀ B : Set X, MeasurableSet B → β Bᶜ = 0 →
      ν P + (μ-ν) univ ≤ ν B) :
    ∃ Q : Set X, StrictSurplusCarrier (μ-ρ+β) ν Q ∧
      ν P + (μ-ν) univ ≤ ν Q := by
  let : IsFiniteMeasure (μ-ρ) := isFiniteMeasure_of_le μ Measure.sub_le
  obtain ⟨hδ,_,_⟩ := excess_relocation_complementarity μ ν ρ β hρ hmass hmin
  obtain ⟨B,hB,hβB,hνB⟩ := exists_ac_full_carrier ν β
  obtain ⟨Q,hQ⟩ := exists_strictSurplusCarrier (μ-ρ+β) ν
  refine ⟨Q,hQ,(hspread B hB hβB).trans (hQ.maximal_reference_volume hB ?_)⟩
  apply hνB.trans
  apply Measure.absolutelyContinuous_of_le
  rw [hδ]
  exact Measure.le_add_left le_rfl

end WeakHessian
end

end OAI
