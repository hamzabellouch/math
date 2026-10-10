import OAI.Analysis.CircleDomains.Topology.ClosedRelationNeighborhood
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Group.InfiniteSum

namespace OAI

/-! Compact source sets uniformly control the centers of late shrinking
balls that meet a fixed neighborhood. Applied to a closed correspondence,
this controls every scalar interval of such a ball, not just its center. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem nonnegative_square_summable_tendsto_zero {d : ℕ → ℝ}
    (hd : ∀ j, 0 ≤ d j) (hs : Summable (fun j => d j^2)) :
    Tendsto d atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hs.tendsto_atTop_zero.eventually (gt_mem_nhds (sq_pos_of_pos hε))] with j hj
  rw [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (hd j)]
  nlinarith

 theorem shrinking_balls_near_compact {X : Type*} [PseudoMetricSpace X]
    {K W : Set X} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (c : ℕ → X) {d : ℕ → ℝ} (hd : Tendsto d atTop (𝓝 0)) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ ∃ N : ℕ, ∀ j, N ≤ j →
      ∀ z ∈ V, z ∈ ball (c j) (d j) → c j ∈ W := by
  obtain ⟨δ,hδ,hsub⟩ := hK.exists_cthickening_subset_open hW hKW
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hd.eventually (gt_mem_nhds (half_pos hδ)))
  refine ⟨thickening (δ/2) K,isOpen_thickening,self_subset_thickening (half_pos hδ) K,N,?_⟩
  intro j hj z hz hball
  obtain ⟨k,hk,hzk⟩ := mem_thickening_iff.mp hz
  apply hsub
  apply mem_cthickening_of_dist_le (c j) k δ K hk
  have hcz : dist (c j) z < d j := by simpa only [mem_ball,dist_comm] using hball
  exact (dist_triangle _ _ _).trans ((add_lt_add hcz hzk).le.trans (by linarith [hN j hj]))

 theorem closed_relation_shrinking_intervals {X Y : Type*} [PseudoMetricSpace X]
    [TopologicalSpace Y] [CompactSpace Y] {R : X → Y → Prop}
    (hR : IsClosed {p : X × Y | R p.1 p.2}) {φ : Y → ℝ} (hφ : Continuous φ)
    {K : Set X} (hK : IsCompact K) {a b η : ℝ} (hη : 0 < η)
    (hmargin : ∀ q ∈ K, ∀ p, R q p → φ p ∈ Ioo (a+η) (b-η))
    (c : ℕ → X) {d ε : ℕ → ℝ} (hd : Tendsto d atTop (𝓝 0))
    (hε : Tendsto ε atTop (𝓝 0)) (I : ℕ → Set ℝ)
    (hI : ∀ j t, t ∈ I j → ∃ p, R (c j) p ∧ |t-φ p| ≤ ε j) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ ∃ N : ℕ, ∀ j, N ≤ j →
      ∀ z ∈ V, z ∈ ball (c j) (d j) → I j ⊆ Ioo a b := by
  obtain ⟨W,hW,hKW,hw⟩ := closed_relation_neighborhood hR
    (isOpen_Ioo.preimage hφ) hmargin
  obtain ⟨V,hV,hKV,N,hN⟩ := shrinking_balls_near_compact hK hW hKW c hd
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hε.eventually (gt_mem_nhds hη))
  refine ⟨V,hV,hKV,max N M,?_⟩
  intro j hj z hz hbz t ht
  obtain ⟨p,hp,hpt⟩ := hI j t ht
  have hpm := hw (c j) (hN j ((le_max_left _ _).trans hj) z hz hbz) p hp
  have hεj := hM j ((le_max_right _ _).trans hj)
  have habs := abs_le.mp hpt
  constructor <;> linarith [hpm.1,hpm.2,habs.1,habs.2]

end CircleDomainRigidity

end

end OAI
