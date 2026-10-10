import OAI.Probability.GaussianPropeller.Elimination

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Reduction

theorem all_partition_bound (d:ℕ) (hd:0<d) :
    ∀ k (A:Fin k→Set (Space d)), IsPartition A → value A≤9/(8*Real.pi) := by
  classical
  let : NeZero d := ⟨by omega⟩
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro A hA
    by_cases hk:k≤3
    · exact partition_bound_small hk hA
    let : NeZero k := ⟨by omega⟩
    obtain ⟨B,hB⟩:=exists_minimal_optimal (d:=d) (k:=k)
    suffices hb:value B≤9/(8*Real.pi) from (hB.1.2 _ hA).trans hb
    by_contra hn
    have hC:9/(8*Real.pi)<value B := lt_of_not_ge hn
    by_cases hall:∀ j,gaussian d (B j)≠0
    · obtain ⟨D⟩:=exists_configuration (by omega) hB hC hall
      by_cases hk4:k=4
      · subst k
        exact D.impossible_four
      · exact D.impossible_five_or_more (by omega)
    · push Not at hall
      obtain ⟨i,hi⟩:=hall
      cases k with
      | zero => omega
      | succ m =>
        have hp:=remove_null_partition hB.1.1 i hi
        have hv:=ih m (by omega) (fun j=>B (i.succAbove j)) hp
        rw [remove_null_value i hi] at hv
        exact (not_le_of_gt hC) hv

end GaussianPropeller.Reduction

namespace GaussianPropeller

theorem main_bound : MainBound := by
  intro n hn A hA
  exact Reduction.all_partition_bound n (by omega) (n+1) A hA

theorem all_partitions : AllPartitions := by
  constructor
  · intro d k hd hk A hA
    exact Reduction.all_partition_bound d hd k A hA
  · exact Reduction.propeller_attainment

end GaussianPropeller

namespace GaussianPropeller

theorem all_partition_bound_nullMeasurable {d k : ℕ} (hd : 0 < d)
    (A : Fin k → Set (Space d))
    (hA : ∀ i, NullMeasurableSet (A i) (gaussian d))
    (hp : ∀ᵐ x ∂gaussian d, ∃! i, x ∈ A i) :
    value A ≤ 9 / (8 * Real.pi) := by
  let B : Fin k → Set (Space d) := fun i => toMeasurable (gaussian d) (A i)
  have he : ∀ i, B i =ᵐ[gaussian d] A i := fun i => (hA i).toMeasurable_ae_eq
  have hB : IsPartition B := by
    refine ⟨fun i => measurableSet_toMeasurable _ _, ?_⟩
    have hh := ae_all_iff.mpr he
    filter_upwards [hp,hh] with x hx heq
    change ∀ i, (x ∈ B i) = (x ∈ A i) at heq
    obtain ⟨i,hi,hu⟩ := hx
    exact ⟨i,Eq.mpr (heq i) hi,fun j hj => hu j (Eq.mp (heq j) hj)⟩
  rw [←Reduction.value_congr_ae he]
  exact Reduction.all_partition_bound d hd k B hB

theorem main_bound_nullMeasurable (n : ℕ) (hn : 4 ≤ n)
    (A : Fin (n+1) → Set (Space n))
    (hA : ∀ i, NullMeasurableSet (A i) (gaussian n))
    (hp : ∀ᵐ x ∂gaussian n, ∃! i, x ∈ A i) :
    value A ≤ 9 / (8 * Real.pi) :=
  all_partition_bound_nullMeasurable (by omega) A hA hp

end GaussianPropeller

end OAI
