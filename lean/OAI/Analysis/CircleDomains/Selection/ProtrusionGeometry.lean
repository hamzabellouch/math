import OAI.Analysis.CircleDomains.Transfer.RealEndCorrespondence
import OAI.Analysis.CircleDomains.Topology.ComponentLocalization

namespace OAI

/-! Initial geometric localization of a marked component protruding beyond its round disk. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

/-- A compact planar set extending beyond a round disk has a boundary point
beyond that disk. No boundary regularity is required. -/
theorem exists_frontier_point_outside_closedBall
    {K : Set ℂ} (hK : IsCompact K) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hnot : ¬ K ⊆ closedBall c r) :
    ∃ x ∈ frontier K, r < dist x c := by
  obtain ⟨y, hy, hyn⟩ := Set.not_subset.mp hnot
  have hyr : r < ‖y - c‖ := by simpa only [mem_closedBall, dist_eq_norm, not_le] using hyn
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn ⟨y, hy⟩
    ((continuous_id.sub continuous_const).norm.continuousOn)
  have hxr : r < ‖x - c‖ := hyr.trans_le (hmax hy)
  have hd : 0 < ‖x - c‖ := hr.trans_lt hxr
  refine ⟨x, ⟨subset_closure hx, ?_⟩, ?_⟩
  · intro hi
    obtain ⟨δ, hδ, hδK⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hi)
    let t := δ / (2 * ‖x - c‖)
    have ht : 0 < t := div_pos hδ (mul_pos (by norm_num) hd)
    have htval : t * ‖x - c‖ = δ / 2 := by
      dsimp only [t]
      field_simp
    let z : ℂ := x + t • (x - c)
    have hzx : z - x = t • (x - c) := by dsimp only [z]; abel
    have hzc : z - c = (1 + t) • (x - c) := by dsimp only [z]; module
    have hzδ : z ∈ ball x δ := by
      rw [mem_ball, dist_eq_norm, hzx, norm_smul, Real.norm_eq_abs, abs_of_pos ht, htval]
      linarith
    have hh : ‖z - c‖ ≤ ‖x - c‖ := hmax (hδK hzδ)
    rw [hzc, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 + t)] at hh
    nlinarith [mul_pos ht hd]
  · simpa only [dist_eq_norm] using hxr

/-- Every boundary point of a complementary component can be approached
from the planar domain. -/
theorem frontier_complement_component_subset_closure
    {U : Set ℂ} (hU : IsOpen U) {q : ℂ} (hq : q ∈ Uᶜ) :
    frontier (connectedComponentIn Uᶜ q) ⊆ closure U := by
  have hK : IsClosed (connectedComponentIn Uᶜ q) := by
    rw [connectedComponentIn_eq_image hq]
    exact hU.isClosed_compl.isClosedMap_subtype_val _ isClosed_connectedComponent
  intro x hx
  have hxK : x ∈ connectedComponentIn Uᶜ q := hK.closure_eq ▸ hx.1
  by_contra hxc
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (isClosed_closure.isOpen_compl.mem_nhds hxc)
  have hballU : ball x δ ⊆ Uᶜ := by
    intro z hz hzu
    exact hball hz (subset_closure hzu)
  have hballK := (convex_ball x δ).isPreconnected.subset_connectedComponentIn
    (mem_ball_self hδ) hballU
  rw [← connectedComponentIn_eq hxK] at hballK
  exact hx.2 (interior_maximal hballK isOpen_ball (mem_ball_self hδ))

/-- A genuine closed domain ball can be placed arbitrarily near a boundary
point of a complementary component. -/
theorem exists_domain_ball_near_component_frontier
    {U : Set ℂ} (hU : IsOpen U) {q : ℂ} (hq : q ∈ Uᶜ)
    {x : ℂ} (hx : x ∈ frontier (connectedComponentIn Uᶜ q))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (a : ℂ) (s : ℝ), 0 < s ∧ closedBall a s ⊆ U ∩ ball x ρ := by
  have hxc := frontier_complement_component_subset_closure hU hq hx
  obtain ⟨a, ha, hax⟩ := Metric.mem_closure_iff.mp hxc ρ hρ
  have haB : a ∈ ball x ρ := by simpa only [mem_ball, dist_comm] using hax
  exact ⟨a, Metric.nhds_basis_closedBall.mem_iff.mp
    ((hU.inter isOpen_ball).mem_nhds ⟨ha, haB⟩)⟩

/-- A protruding continuum has a small nontrivial subcontinuum separated
from its marked round disk, with a fixed pair of nested neighborhoods. -/
theorem exists_local_protrusion
    {K : Set ℂ} (hK : IsCompact K) (hconn : IsConnected K)
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r) (hDK : closedBall c r ⊆ K)
    (hne : K ≠ closedBall c r) :
    ∃ (x : ℂ) (ρ : ℝ) (Q : Set ℂ),
      0 < ρ ∧ x ∈ frontier K ∧
      Disjoint (closedBall x (2 * ρ)) (closedBall c r) ∧
      IsCompact Q ∧ IsConnected Q ∧ Q.Nontrivial ∧ x ∈ Q ∧
      Q ⊆ K ∩ ball x ρ := by
  have hnot : ¬ K ⊆ closedBall c r := fun h => hne (Subset.antisymm h hDK)
  obtain ⟨x, hx, hdist⟩ := exists_frontier_point_outside_closedBall hK hr hnot
  have hxD : x ∉ closedBall c r := by simpa only [mem_closedBall, not_le] using hdist
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (isClosed_closedBall.isOpen_compl.mem_nhds hxD)
  let ρ := δ / 4
  have hρ : 0 < ρ := div_pos hδ (by norm_num)
  have hd : Disjoint (closedBall x (2 * ρ)) (closedBall c r) := by
    apply Set.disjoint_left.mpr
    intro z hz hzD
    apply hball ?_ hzD
    have hz' : dist z x ≤ 2 * ρ := hz
    change dist z x < δ
    dsimp only [ρ] at hz'
    linarith
  have hnt : K.Nontrivial := by
    refine ⟨x, hK.isClosed.closure_eq ▸ hx.1, c, hDK (mem_closedBall_self hr), ?_⟩
    intro h
    subst x
    simp only [dist_self] at hdist
    linarith
  obtain ⟨Q, hQc, hQconn, hQnt, hxQ, hQsub⟩ := exists_nontrivial_subcontinuum_in_open
    hK hconn hnt (hK.isClosed.closure_eq ▸ hx.1) isOpen_ball (mem_ball_self hρ)
  exact ⟨x, ρ, Q, hρ, hx, hd, hQc, hQconn, hQnt, hxQ, hQsub⟩

end CircleDomainRigidity

end

end OAI
