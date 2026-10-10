import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
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
open MeasureTheory Filter Set
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

lemma exists_bounded_rn_restriction (μ δ : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure δ] (hac : μ ≪ δ)
    {r : ℝ≥0∞} (hr : r < μ univ) :
    ∃ (A : Set X) (n : ℕ), MeasurableSet A ∧ 0 < n ∧ r < μ A ∧
      μ.restrict A ≤ (n : ℝ≥0∞) • δ := by
  let A : ℕ → Set X := fun n => {x | μ.rnDeriv δ x ≤ (n+1 : ℕ)}
  have hA n : MeasurableSet (A n) := measurableSet_le (μ.measurable_rnDeriv δ) measurable_const
  have hmono : Monotone A := by
    intro i j hij x hx
    change μ.rnDeriv δ x ≤ ((i+1 : ℕ) : ℝ≥0∞) at hx
    change μ.rnDeriv δ x ≤ ((j+1 : ℕ) : ℝ≥0∞)
    exact hx.trans (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hfull : μ (⋃ n, A n) = μ univ := by
    apply measure_congr
    filter_upwards [hac.ae_le (μ.rnDeriv_lt_top δ)] with x hx
    apply propext
    simp only [mem_iUnion,mem_univ,iff_true]
    change ∃ n, μ.rnDeriv δ x ≤ ((n+1 : ℕ) : ℝ≥0∞)
    obtain ⟨n,hn⟩ := ENNReal.exists_nat_gt hx.ne
    exact ⟨n,hn.le.trans (by exact_mod_cast Nat.le_succ n)⟩
  rw [hmono.measure_iUnion] at hfull
  obtain ⟨n,hn⟩ := lt_iSup_iff.mp (hr.trans_le hfull.ge)
  refine ⟨A n,n+1,hA n,Nat.succ_pos n,hn,?_⟩
  calc
    μ.restrict (A n) = (δ.restrict (A n)).withDensity (μ.rnDeriv δ) := by
      rw [← restrict_withDensity (hA n),μ.withDensity_rnDeriv_eq δ hac]
    _ ≤ (δ.restrict (A n)).withDensity (fun _ => (n+1 : ℕ)) := by
      apply withDensity_mono
      exact (ae_restrict_mem (hA n)).mono (fun x hx => hx)
    _ = ((n+1 : ℕ) : ℝ≥0∞) • δ.restrict (A n) := withDensity_const _
    _ ≤ _ := smul_le_smul_left _ Measure.restrict_le_self

lemma exists_bounded_rn_subrestriction (μ δ : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure δ] {P : Set X} (hP : MeasurableSet P)
    (hac : μ.restrict P ≪ δ) {r : ℝ≥0∞} (hr : r < μ P) :
    ∃ (A : Set X) (n : ℕ), MeasurableSet A ∧ A ⊆ P ∧ 0 < n ∧ r < μ A ∧
      μ.restrict A ≤ (n : ℝ≥0∞) • δ := by
  obtain ⟨A,n,hA,hn,hrA,hdom⟩ := exists_bounded_rn_restriction (μ.restrict P) δ hac
    (by simpa using hr)
  refine ⟨A ∩ P,n,hA.inter hP,inter_subset_right,hn,?_,?_⟩
  · simpa only [Measure.restrict_apply hA] using hrA
  · simpa only [Measure.restrict_restrict hA] using hdom

end WeakHessian
end
end InlinedFile0

end OAI
