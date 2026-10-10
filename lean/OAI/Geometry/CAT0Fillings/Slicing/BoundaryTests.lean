import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.CountableTests

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

namespace CAT0Fillings.Foundations
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {k : ℕ}
omit [BorelSpace X] in
lemma IsMetricCurrent.boundary_testClass_continuous {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (K : ℕ) :
    Continuous (TestClass.eval (X := X) (K := K) (boundarySucc T)) := by
  apply continuous_iff_seqContinuous.mpr
  intro ps p hp
  have had (q : TestClass (X := X) k K) : Admissible (q.val.1 : X → ℝ) (fun i => q.val.2 i) :=
    ⟨q.boundedLip,fun i => ⟨K,q.property.2.2 i⟩⟩
  simp only [Function.comp_def,TestClass.eval,boundarySucc,ite_eq_left (had _)]
  apply hT.sequentialContinuity _ _ _ (BoundedLip.const 1)
  · intro i
    exact ⟨K,fun n => Fin.cases (ps n).property.1 (fun j => (ps n).property.2.2 j) i⟩
  · intro i x
    refine Fin.cases ?_ (fun j => ?_) i
    · have hc : Continuous (fun q : TestClass (X := X) k K => q.val.1 x) := by fun_prop
      exact hc.continuousAt.tendsto.comp hp
    · have hc : Continuous (fun q : TestClass (X := X) k K => q.val.2 j x) := by fun_prop
      exact hc.continuousAt.tendsto.comp hp

theorem ae_boundary_eq_of_ae_test_eq {A : Type*} [MeasurableSpace A] (μ : Measure A)
    {S : A → Functional X (k+1)} {T : A → Functional X k}
    (hS : ∀ᵐ a ∂μ, IsMetricCurrent (S a)) (hT : ∀ᵐ a ∂μ, IsMetricCurrent (T a))
    (he : ∀ b π, Admissible b π → ∀ᵐ a ∂μ, boundarySucc (S a) b π = T a b π) :
    ∀ᵐ a ∂μ, boundarySucc (S a) = T a := by
  choose p hp using fun K : ℕ => TopologicalSpace.exists_dense_seq (TestClass (X := X) k K)
  have ha K j : Admissible ((p K j).val.1 : X → ℝ) (fun i => (p K j).val.2 i) :=
    ⟨(p K j).boundedLip,fun i => ⟨K,(p K j).property.2.2 i⟩⟩
  have hc : ∀ᵐ a ∂μ, ∀ K j, TestClass.eval (boundarySucc (S a)) (p K j) = TestClass.eval (T a) (p K j) :=
    ae_all_iff.mpr fun K => ae_all_iff.mpr fun j => he _ _ (ha K j)
  filter_upwards [hS,hT,hc] with a hs ht h
  have hh K : TestClass.eval (K := K) (boundarySucc (S a)) = TestClass.eval (K := K) (T a) := by
    apply (hp K).equalizer (IsMetricCurrent.boundary_testClass_continuous hs K) (IsMetricCurrent.testClass_continuous ht K)
    funext j; exact h K j
  funext b π
  by_cases hab : Admissible b π
  · obtain ⟨K,q,hb,hπ⟩ := admissible_mem_testClass hab
    have hz := congrFun (hh K) q
    simpa only [TestClass.eval,hb,hπ] using hz
  · rw [ht.offDomain b π hab,boundarySucc,ite_eq_right hab]

end CAT0Fillings.Foundations
end

end OAI
