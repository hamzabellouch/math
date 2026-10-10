import OAI.NumberTheory.DukePrimeDegree.Geometry.AtomlessDiagonalMeasure
import OAI.NumberTheory.DukePrimeDegree.Dynamics.UnboundedReturnSection
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

namespace OAI

/-! # Small positive sections inside a prescribed coordinate chart -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DukePrimeDegree

lemma exists_small_positive_subset
    {Y : Type*} [MetricSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {A : Set Y} (hA : MeasurableSet A) (hAp : μ A ≠ 0)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ S : Set Y, MeasurableSet S ∧ S ⊆ A ∧ μ S ≠ 0 ∧ μ S ≤ ε := by
  let ν := μ.restrict A
  have hν : ν ≠ 0 := by
    intro h
    have h' := congrArg (fun m : Measure Y => m univ) h
    apply hAp
    simpa [ν] using h'
  obtain ⟨x,hx⟩ := ν.nonempty_support hν
  obtain ⟨U,hxU,hU,hμU⟩ := ({x} : Set Y).exists_isOpen_lt_of_lt (μ := ν) ε
    (by simpa only [measure_singleton] using hε)
  have hpos : 0 < ν U := (Measure.mem_support_iff_forall x).mp hx U
    (hU.mem_nhds (hxU (mem_singleton x)))
  refine ⟨A ∩ U,hA.inter hU.measurableSet,inter_subset_left,?_,?_⟩
  · have he : μ (A ∩ U)=ν U := by
      change μ (A ∩ U)=(μ.restrict A) U
      rw [Measure.restrict_apply hU.measurableSet,inter_comm]
    rw [he]
    exact hpos.ne'
  · have he : μ (A ∩ U)=ν U := by
      change μ (A ∩ U)=(μ.restrict A) U
      rw [Measure.restrict_apply hU.measurableSet,inter_comm]
    rw [he]
    exact hμU.le

theorem exists_small_positive_unbounded_return_section
    {Y : Type*} [MetricSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {T : Y → Y} (hT : Ergodic T μ) (hE : MeasurableEmbedding T)
    {A : Set Y} (hA : MeasurableSet A) (hAp : μ A ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Set Y, MeasurableSet S ∧ S ⊆ A ∧ μ S ≠ 0 ∧ μ.real S ≤ ε ∧
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ μ (firstReturnLevel T S n) ≠ 0 := by
  obtain ⟨B,hB,hBA,hBp,hBε⟩ := exists_small_positive_subset μ hA hAp
    (ENNReal.ofReal_pos.mpr hε)
  have hsmall : ∀ δ : ℝ≥0∞, 0 < δ → δ ≠ ∞ →
      ∃ E : Set Y, MeasurableSet E ∧ μ E ≠ 0 ∧ μ E ≤ δ := by
    intro δ hδ _
    obtain ⟨E,hE,_,hEp,hEδ⟩ := exists_small_positive_subset μ
      MeasurableSet.univ (by simp) hδ
    exact ⟨E,hE,hEp,hEδ⟩
  obtain ⟨S,hS,hSB,hSp,htail⟩ := exists_unbounded_return_section μ hT hE hsmall hB hBp
  refine ⟨S,hS,hSB.trans hBA,hSp,?_,htail⟩
  exact (ENNReal.toReal_mono (by finiteness) ((measure_mono hSB).trans hBε)).trans_eq
    (ENNReal.toReal_ofReal hε.le)

end DukePrimeDegree

end

end OAI
