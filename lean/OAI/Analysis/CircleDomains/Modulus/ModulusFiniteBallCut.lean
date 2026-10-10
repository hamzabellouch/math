import OAI.Analysis.CircleDomains.Probability.MeasureFamilyIncreasing
import Mathlib.Topology.MetricSpace.Pseudo.Basic

namespace OAI

/-! A finite collection of small closed balls retains a prescribed strict
modulus threshold in a separable metric presentation. -/
open Set Function Filter MeasureTheory TopologicalSpace Metric
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_modulus_finite_closedBall_cut
    {X Z : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
    [MeasurableSpace Z] (σ : Measure Z) [IsSeparable σ] (K : X → FiniteMeasure Z)
    {C : Set X} {c : ℝ≥0∞} (hc : c < measureFamilyModulus C Z σ (fun x => K x.val))
    {r : ℝ} (hr : 0 < r) :
    ∃ N : ℕ, c < measureFamilyModulus
      ((C ∩ ⋃ j ∈ (↑(Finset.range (N+1)) : Set ℕ), closedBall (denseSeq X j) r) : Set X)
      Z σ (fun x => K x.val) := by
  let S : ℕ → Set C := fun N => {x | ∃ j ≤ N, dist x.val (denseSeq X j) ≤ r}
  have hm : Monotone S := by
    intro n m hnm x hx
    obtain ⟨j,hj,hxj⟩ := hx
    exact ⟨j,hj.trans hnm,hxj⟩
  have hu : ∀ x : C, ∃ n, x ∈ S n := by
    intro x
    obtain ⟨j,hj⟩ := Metric.denseRange_iff.mp (denseRange_denseSeq X) x.val r hr
    exact ⟨j,j,le_rfl,hj.le⟩
  rw [measureFamilyModulus_iUnion σ (fun x : C => K x.val) S hm hu] at hc
  obtain ⟨N,hN⟩ := lt_iSup_iff.mp hc
  refine ⟨N,?_⟩
  have hrange : range (fun x : S N => K x.val.val) =
      range (fun x : ((C ∩ ⋃ j ∈ (↑(Finset.range (N+1)) : Set ℕ),
        closedBall (denseSeq X j) r) : Set X) => K x.val) := by
    ext v
    constructor
    · rintro ⟨x,hx⟩
      obtain ⟨j,hj,hxj⟩ := x.property
      exact ⟨⟨x.val.val,x.val.property,mem_iUnion₂.mpr
        ⟨j,by simpa only [Finset.mem_coe,Finset.mem_range] using Nat.lt_succ_of_le hj,hxj⟩⟩,hx⟩
    · rintro ⟨x,hx⟩
      obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp x.property.2
      have hjN : j ≤ N := Nat.le_of_lt_succ (by simpa only [Finset.mem_coe,Finset.mem_range] using hj)
      exact ⟨⟨⟨x.val,x.property.1⟩,j,hjN,hxj⟩,hx⟩
  exact hN.trans_eq (measureFamilyModulus_eq_of_range_eq σ _ _ hrange)

end CircleDomainRigidity

end

end OAI
