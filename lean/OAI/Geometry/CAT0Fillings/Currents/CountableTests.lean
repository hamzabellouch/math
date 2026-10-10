import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.WeakCompactness

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

namespace CAT0Fillings
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace Foundations
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
lemma exists_normal_weak_subsequence_of_integral_mass_bound
    {k : ℕ} {Ts : ℕ → Functional X (k+1+1)}
    (hTs : ∀ j, IsIntegral (k+1+1) (Ts j))
    (M N : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M)
    (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N) :
    ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧
      ∃ T : Functional X (k+1+1), IsMetricCurrent T ∧
        IsMetricCurrent (boundarySucc T) ∧ mass T ≤ M ∧
        mass (boundarySucc T) ≤ N ∧
        ∀ b π, Tendsto (fun j => Ts (ψ j) b π) atTop (𝓝 (T b π)) := by
  obtain ⟨l, hl, hle, T, hT, hbd, hTM, hTN, hlim⟩ :=
    exists_normal_weak_cluster_of_integral_mass_bound (l := atTop) hTs M N hM hN
  let := hl
  have hsep (K : ℕ) : ∃ D : ℕ → TestClass (X := X) (k+1+1) K, DenseRange D :=
    TopologicalSpace.exists_dense_seq _
  choose D hD using hsep
  let evaluations (U : Functional X (k+1+1)) : (ℕ × ℕ) → ℝ :=
    fun ij => TestClass.eval U (D ij.1 ij.2)
  have heval : Tendsto (fun j => evaluations (Ts j)) l (𝓝 (evaluations T)) :=
    tendsto_pi_nhds.mpr fun ij => hlim _ _
  obtain ⟨ψ, hψ, hψlim⟩ := (heval.mapClusterPt.mono hle).tendsto_subseq
  refine ⟨ψ, hψ, T, hT, hbd, hTM, hTN, ?_⟩
  have hall (K : ℕ) (p : TestClass (X := X) (k+1+1) K) :
      Tendsto (fun j => TestClass.eval (Ts (ψ j)) p) atTop (𝓝 (TestClass.eval T p)) := by
    let C : ℝ≥0 := (K : ℝ≥0) ^ (k+1+1) * M +
      (k+1+1) * ((K : ℝ≥0) + K) ^ (k+1) * (K * N + K * M)
    have hL (j : ℕ) : LipschitzWith C (TestClass.eval (K := K) (Ts j)) := by
      simpa [C, Nat.cast_add, Nat.cast_one] using IntegerRectifiable.testClass_lipschitz (hTs j).2.1 (hTs j).1 (hTs j).2.2.1 M N
        (hM j) (hN j) K
    have hLlim : LipschitzWith C (TestClass.eval (K := K) T) :=
      lipschitz_of_pointwise_limit (l := l) hL (fun q => hlim q.val.1 (fun i => q.val.2 i))
    apply tendsto_of_lipschitz_dense (fun j => hL (ψ j)) hLlim (hD K) _ p
    intro i
    exact tendsto_pi_nhds.mp hψlim (K, i)
  intro b π
  by_cases hadm : Admissible b π
  · obtain ⟨K, p, hp₁, hp₂⟩ := admissible_mem_testClass hadm
    simpa only [TestClass.eval, hp₁, hp₂] using hall K p
  · have heq : (fun j => Ts (ψ j) b π) = fun _ => 0 :=
      funext fun j => (hTs (ψ j)).1.offDomain b π hadm
    rw [heq, hT.offDomain b π hadm]
    exact tendsto_const_nhds

end Foundations
end CAT0Fillings

namespace CAT0Fillings.Foundations
open MeasureTheory Set Filter
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

lemma IsMetricCurrent.testClass_continuous {d : ℕ} {T : Functional X d}
    (hT : IsMetricCurrent T) (K : ℕ) :
    Continuous (TestClass.eval (X := X) (d := d) (K := K) T) := by
  apply continuous_iff_seqContinuous.mpr
  intro ps p hp
  have hcoord : Tendsto (fun n => T p.val.1 (fun i => (ps n).val.2 i)) atTop
      (𝓝 (T p.val.1 (fun i => p.val.2 i))) := by
    apply hT.sequentialContinuity _ _ _ p.boundedLip
    · intro i
      exact ⟨K,fun n => (ps n).property.2.2 i⟩
    · intro i x
      have hc : Continuous (fun q : TestClass (X := X) d K => q.val.2 i x) := by fun_prop
      exact hc.continuousAt.tendsto.comp hp
  have hd : Tendsto (fun n => dist (ps n) p) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hp
  have hbnd (n : ℕ) :
      dist (T p.val.1 (fun i => (ps n).val.2 i))
        (T (ps n).val.1 (fun i => (ps n).val.2 i)) ≤
      ((K:ℝ)^d * mass T) * dist (ps n) p := by
    have hh := IsMetricCurrent.first_difference_bound hT p.boundedLip (ps n).boundedLip
      (fun i => (ps n).val.2 i) K (ps n).property.2.2 (nndist (ps n) p) (fun x => ?_)
    · simpa only [Real.dist_eq,NNReal.coe_natCast,coe_nndist,mul_assoc,mul_comm,mul_left_comm]
        using hh
    · have h := (ContinuousMap.dist_apply_le_dist (f := (ps n).val.1) (g := p.val.1) x).trans
        (le_max_left (dist (ps n).val.1 p.val.1) (dist (ps n).val.2 p.val.2))
      change dist ((ps n).val.1 x) (p.val.1 x) ≤ dist (ps n) p at h
      simpa only [coe_nndist,Real.dist_eq,abs_sub_comm] using h
  apply tendsto_of_tendsto_of_dist hcoord
  exact squeeze_zero (fun n => dist_nonneg) hbnd (by simpa using hd.const_mul ((K:ℝ)^d * mass T))

theorem exists_countable_current_tests (d : ℕ) :
    ∃ (b : ℕ → ℕ → X → ℝ) (π : ℕ → ℕ → Fin d → X → ℝ),
      (∀ K j, Admissible (b K j) (π K j)) ∧
      ∀ S T : Functional X d, IsMetricCurrent S → IsMetricCurrent T →
        (∀ K j, S (b K j) (π K j) = T (b K j) (π K j)) → S = T := by
  choose p hp using fun K : ℕ => TopologicalSpace.exists_dense_seq (TestClass (X := X) d K)
  refine ⟨fun K j => (p K j).val.1,fun K j i => (p K j).val.2 i,?_,?_⟩
  · intro K j
    exact ⟨(p K j).boundedLip,fun i => ⟨K,(p K j).property.2.2 i⟩⟩
  · intro S T hS hT heq
    have he (K : ℕ) : TestClass.eval (K := K) S = TestClass.eval (K := K) T := by
      apply (hp K).equalizer (IsMetricCurrent.testClass_continuous hS K) (IsMetricCurrent.testClass_continuous hT K)
      funext j
      exact heq K j
    funext b π
    by_cases h : Admissible b π
    · obtain ⟨K,q,hb,hπ⟩ := admissible_mem_testClass h
      have hh := congrFun (he K) q
      simpa only [TestClass.eval,hb,hπ] using hh
    · rw [hS.offDomain b π h,hT.offDomain b π h]

theorem ae_eq_of_ae_test_eq {A : Type*} [MeasurableSpace A] (μ : Measure A)
    {d : ℕ} {S T : A → Functional X d}
    (hS : ∀ᵐ a ∂μ, IsMetricCurrent (S a)) (hT : ∀ᵐ a ∂μ, IsMetricCurrent (T a))
    (he : ∀ b π, Admissible b π → ∀ᵐ a ∂μ, S a b π = T a b π) :
    ∀ᵐ a ∂μ, S a = T a := by
  obtain ⟨b,π,ha,hex⟩ := exists_countable_current_tests (X := X) d
  have hc : ∀ᵐ a ∂μ, ∀ K j, S a (b K j) (π K j) = T a (b K j) (π K j) :=
    ae_all_iff.mpr fun K => ae_all_iff.mpr fun j => he _ _ (ha K j)
  filter_upwards [hS,hT,hc] with a hs ht h
  exact hex _ _ hs ht h

end CAT0Fillings.Foundations

end

end OAI
