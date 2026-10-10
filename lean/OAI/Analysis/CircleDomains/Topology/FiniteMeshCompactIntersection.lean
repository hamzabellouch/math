import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Finite covers at successively smaller radii make the intersection
compact, and let a continuous image commute with the nested closures. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

lemma totallyBounded_diagonal_of_finite_mesh
    (C : ℕ → Set X) (hanti : Antitone C) (F : ℕ → Finset X)
    (hmesh : ∀ n, C (n+1) ⊆ ⋃ z ∈ (↑(F n) : Set X), closedBall z (1/((n:ℝ)+1)))
    (x : ℕ → X) (hx : ∀ n, x n ∈ C n) : TotallyBounded (range x) := by
  classical
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds hε)).exists
  let E : Set X := (↑(F N) : Set X) ∪ (x '' (↑(Finset.range (N+1)) : Set ℕ))
  refine ⟨E,(F N).finite_toSet.union ((Finset.range (N+1)).finite_toSet.image x),?_⟩
  rintro y ⟨k,rfl⟩
  by_cases hk : N+1 ≤ k
  · have hm := hmesh N (hanti hk (hx k))
    obtain ⟨z,hz,hxz⟩ := mem_iUnion₂.mp hm
    apply mem_iUnion₂.mpr
    refine ⟨z,Or.inl hz,?_⟩
    exact (mem_closedBall.mp hxz).trans_lt hN
  · apply mem_iUnion₂.mpr
    refine ⟨x k,Or.inr ⟨k,by simpa only [Finset.mem_coe,Finset.mem_range] using lt_of_not_ge hk,rfl⟩,?_⟩
    simpa only [mem_ball,dist_self] using hε

lemma compact_iInter_of_finite_mesh [CompleteSpace X]
    (C : ℕ → Set X) (hC : ∀ n, IsClosed (C n))
    (F : ℕ → Finset X)
    (hmesh : ∀ n, C (n+1) ⊆ ⋃ z ∈ (↑(F n) : Set X), closedBall z (1/((n:ℝ)+1))) :
    IsCompact (⋂ n, C n) := by
  have ht : TotallyBounded (⋂ n, C n) := by
    apply Metric.totallyBounded_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds hε)).exists
    refine ⟨F N,(F N).finite_toSet,?_⟩
    intro x hx
    obtain ⟨z,hz,hxz⟩ := mem_iUnion₂.mp (hmesh N (mem_iInter.mp hx (N+1)))
    exact mem_iUnion₂.mpr ⟨z,hz,(mem_closedBall.mp hxz).trans_lt hN⟩
  exact ht.isCompact_of_isClosed (isClosed_iInter hC)

lemma image_iInter_eq_iInter_closure_of_finite_mesh [CompleteSpace X]
    (C : ℕ → Set X) (hC : ∀ n, IsClosed (C n)) (hanti : Antitone C)
    (F : ℕ → Finset X)
    (hmesh : ∀ n, C (n+1) ⊆ ⋃ z ∈ (↑(F n) : Set X), closedBall z (1/((n:ℝ)+1)))
    (f : X → Y) (hf : Continuous f) :
    f '' (⋂ n, C n) = ⋂ n, closure (f '' C n) := by
  classical
  apply Subset.antisymm
  · rintro y ⟨x,hx,rfl⟩
    exact mem_iInter.mpr (fun n => subset_closure (mem_image_of_mem f (mem_iInter.mp hx n)))
  · intro y hy
    have hex (n : ℕ) : ∃ x ∈ C n, dist (f x) y < 1/((n:ℝ)+1) := by
      obtain ⟨w,⟨x,hx,rfl⟩,hw⟩ := Metric.mem_closure_iff.mp (mem_iInter.mp hy n)
        (1/((n:ℝ)+1)) (by positivity)
      exact ⟨x,hx,by simpa only [dist_comm] using hw⟩
    choose x hx hd using hex
    have ht := totallyBounded_diagonal_of_finite_mesh C hanti F hmesh x hx
    have hk : IsCompact (closure (range x)) := ht.closure.isCompact_of_isClosed isClosed_closure
    obtain ⟨z,_,ρ,hρ,hlim⟩ := hk.isSeqCompact (fun n => subset_closure (mem_range_self n))
    have hz (n : ℕ) : z ∈ C n := by
      apply (hC n).mem_of_tendsto hlim
      filter_upwards [hρ.tendsto_atTop.eventually (eventually_ge_atTop n)] with k hk
      exact hanti hk (hx (ρ k))
    have hfy : Tendsto (fun n => f (x (ρ n))) atTop (𝓝 y) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      exact squeeze_zero (fun n => dist_nonneg) (fun n => (hd (ρ n)).le)
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hρ.tendsto_atTop)
    have heq : f z = y := tendsto_nhds_unique (hf.continuousAt.tendsto.comp hlim) hfy
    exact ⟨z,mem_iInter.mpr hz,heq⟩

end CircleDomainRigidity

end

end OAI
