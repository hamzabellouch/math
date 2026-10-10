import OAI.Analysis.CircleDomains.Topology.InactiveCollars
import OAI.Analysis.CircleDomains.Selection.OuterContours
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

/-!
# Connected compact neighborhoods of filling boundaries

Small closed metric thickenings of a compact connected planar curve
are connected and compact. They give connected collars inside any
prescribed open boundary neighborhood, as required for simultaneous
staircase inactivity. No smooth tubular-neighborhood theorem is needed.
-/

open Set Filter Metric
open scoped Topology

namespace CircleDomainRigidity.FiniteTransfer

theorem isConnected_cthickening
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (hc : IsCompact C) (hconn : IsConnected C) {δ : ℝ} (hδ : 0 ≤ δ) :
    IsConnected (cthickening δ C) := by
  obtain ⟨x, hx⟩ := hconn.nonempty
  have hp : IsPreconnected (⋃ z : C, C ∪ closedBall (z : E) δ) := by
    apply isPreconnected_iUnion
    · exact ⟨x, mem_iInter.mpr (fun _ => Or.inl hx)⟩
    · intro z
      exact hconn.isPreconnected.union (z : E) z.property (mem_closedBall_self hδ)
        isPreconnected_closedBall
  have heq : (⋃ z : C, C ∪ closedBall (z : E) δ) = cthickening δ C := by
    rw [hc.cthickening_eq_biUnion_closedBall hδ]
    ext y
    constructor
    · intro hy
      obtain ⟨z, hy⟩ := mem_iUnion.mp hy
      rcases hy with hy | hy
      · exact mem_iUnion₂.mpr ⟨y, hy, mem_closedBall_self hδ⟩
      · exact mem_iUnion₂.mpr ⟨z, z.property, hy⟩
    · intro hy
      obtain ⟨z, hz, hy⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion.mpr ⟨⟨z, hz⟩, Or.inr hy⟩
  exact ⟨⟨x, self_subset_cthickening C hx⟩, heq ▸ hp⟩

theorem exists_compact_connected_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {C U : Set E} (hc : IsCompact C) (hconn : IsConnected C)
    (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ K : Set E, IsCompact K ∧ IsConnected K ∧ K ∈ 𝓝ˢ C ∧ K ⊆ U := by
  obtain ⟨δ, hδ, hsub⟩ := hc.exists_cthickening_subset_open hU hCU
  exact ⟨cthickening δ C, hc.cthickening, isConnected_cthickening hc hconn hδ.le,
    cthickening_mem_nhdsSet C hδ, hsub⟩

/-- A connected compact collar may be kept inside the domain, inside
the relevant mask, and away from every inactive grid by choosing `U`
to be the intersection of those open boundary neighborhoods. -/
theorem exists_compact_connected_jordan_collar
    (H : ℂ ≃ₜ ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hboundary : frontier (jordanInterior H) ⊆ U) :
    ∃ K : Set ℂ, IsCompact K ∧ IsConnected K ∧
      K ∈ 𝓝ˢ (frontier (jordanInterior H)) ∧ K ⊆ U := by
  apply exists_compact_connected_neighborhood
    ((isCompact_closure_jordanInterior H).of_isClosed_subset isClosed_frontier frontier_subset_closure)
    (isConnected_frontier_jordanInterior H) hU hboundary

end CircleDomainRigidity.FiniteTransfer

end OAI
