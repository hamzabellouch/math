import Mathlib
import OAI.Geometry.IntegralFillings.Currents.CountableTests

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings.Foundations
open MeasureTheory Set Filter
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
abbrev UnitTestClass (d K : ℕ) :=
  {p : TestClass (X := X) d K // ∀ i, LipschitzWith 1 (p.val.2 i)}

instance unitTestClass_nonempty (d K : ℕ) : Nonempty (UnitTestClass (X := X) d K) := by
  refine ⟨⟨⟨(0,fun _ => 0),?_,?_,?_⟩,?_⟩⟩
  · exact (LipschitzWith.const 0).weaken (by positivity)
  · simp
  · intro i
    exact (LipschitzWith.const 0).weaken (by positivity)
  · intro i
    exact (LipschitzWith.const 0).weaken (by positivity)

lemma TestClass.continuous_integral_abs (d K : ℕ) (μ : Measure X) [IsFiniteMeasure μ] :
    Continuous (fun p : TestClass (X := X) d K => ∫ x, |p.val.1 x| ∂μ) := by
  apply continuous_of_dominated (bound := fun _ => (K:ℝ))
  · intro p
    exact p.val.1.continuous.abs.measurable.aestronglyMeasurable
  · intro p
    exact Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs,abs_abs] using (p.val.1.norm_coe_le_norm x).trans p.property.2.1
  · exact integrable_const _
  · exact Eventually.of_forall fun x => by fun_prop

theorem exists_countable_mass_tests (d : ℕ) :
    ∃ (b : ℕ → ℕ → X → ℝ) (π : ℕ → ℕ → Fin d → X → ℝ),
      (∀ K j, BoundedLip (b K j) ∧ ∀ i, LipschitzWith 1 (π K j i)) ∧
      ∀ T : Functional X d, IsMetricCurrent T →
        ∀ μ : Measure X, IsFiniteMeasure μ →
          (∀ K j, |T (b K j) (π K j)| ≤ ∫ x, |b K j x| ∂μ) → Controls T μ := by
  choose p hp using fun K : ℕ => TopologicalSpace.exists_dense_seq (UnitTestClass (X := X) d K)
  refine ⟨fun K j => (p K j).val.val.1,fun K j i => (p K j).val.val.2 i,?_,?_⟩
  · intro K j
    exact ⟨(p K j).val.boundedLip,(p K j).property⟩
  · intro T hT μ hμ he b π hb hπ
    let := hμ
    obtain ⟨K,q,hbq,hπq⟩ := admissible_mem_testClass (show Admissible b π from ⟨hb,fun i => ⟨1,hπ i⟩⟩)
    let q' : UnitTestClass (X := X) d K := ⟨q,by
      intro i
      have hi : (q.val.2 i : X → ℝ) = π i := congrFun hπq i
      simpa only [hi] using hπ i⟩
    have hh : |TestClass.eval T q'.val| ≤ ∫ x, |q'.val.val.1 x| ∂μ := by
      apply (hp K).induction_on (p := fun r : UnitTestClass (X := X) d K =>
        |TestClass.eval T r.val| ≤ ∫ x, |r.val.val.1 x| ∂μ) q'
      · apply isClosed_le
        · exact ((IsMetricCurrent.testClass_continuous hT K).comp continuous_subtype_val).abs
        · exact (TestClass.continuous_integral_abs d K μ).comp continuous_subtype_val
      · intro j
        exact he K j
    simpa only [q',TestClass.eval,hbq,hπq] using hh

theorem ae_controls_of_testwise_bound {A : Type*} [MeasurableSpace A] (ν : Measure A)
    {d : ℕ} {T : A → Functional X d} {μ : A → Measure X}
    (hT : ∀ᵐ a ∂ν, IsMetricCurrent (T a))
    (hμ : ∀ᵐ a ∂ν, IsFiniteMeasure (μ a))
    (hb : ∀ b π, BoundedLip b → (∀ i, LipschitzWith 1 (π i)) →
      ∀ᵐ a ∂ν, |T a b π| ≤ ∫ x, |b x| ∂μ a) :
    ∀ᵐ a ∂ν, Controls (T a) (μ a) := by
  obtain ⟨b,π,ht,hd⟩ := exists_countable_mass_tests (X := X) d
  have hc : ∀ᵐ a ∂ν, ∀ K j, |T a (b K j) (π K j)| ≤ ∫ x, |b K j x| ∂μ a :=
    ae_all_iff.mpr fun K => ae_all_iff.mpr fun j => hb _ _ (ht K j).1 (ht K j).2
  filter_upwards [hT,hμ,hc] with a hta hma hca
  exact hd _ hta _ hma hca

end SharpIntegralFillings.Foundations
end

end OAI
