import OAI.Analysis.CircleDomains.Transfer.CoreCrossing
import OAI.Analysis.CircleDomains.Selection.DustCover

namespace OAI

/-!
# Topology of finite-length level unions

The compact spaces here are a quotient level union and its physical
preimage, with the induced metrics. Thus finite Hausdorff length on
`G` is finite physical level length, not finite length of a planar open
domain. Compact totally disconnected quotient dust supplies the small
disjoint covers and hence compact physical cores. All counting and
local connectedness conclusions are then proved.
-/

open Set Metric MeasureTheory Function
open scoped ENNReal

namespace CircleDomainRigidity

/-- Finite physical length and compact totally disconnected quotient
dust imply the finite bound on disjoint large subcontinua. -/
theorem finite_large_continuum_bound_of_compact_quotient_dust
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (π : Y → X) (hπ : Continuous π) (hsurj : Function.Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x})) {G : Set Y} (hG : IsOpen G)
    {B : Set X} (hB : IsCompact B) (hTD : IsTotallyDisconnected B)
    (hdust : π '' Gᶜ ⊆ B) (hlength : (μH[1] : Measure Y) G < ∞) :
    HasFiniteLargeContinuumBound X := by
  apply finite_large_continuum_bound_of_compact_cores π hπ hsurj hfiber hG hlength
  intro ε hε
  obtain ⟨n, U, hopen, hcoverB, hdisj, hsmall⟩ :=
    exists_small_disjoint_open_cover_of_compact_dust hB hTD hε
  let K : Set Y := π ⁻¹' (⋃ i, U i)ᶜ
  have hK : IsCompact K := ((isOpen_iUnion hopen).isClosed_compl.preimage hπ).isCompact
  have hKG : K ⊆ G := by
    intro p hp
    by_contra hpG
    have hpB : π p ∈ B := hdust ⟨p, hpG, rfl⟩
    exact hp (hcoverB hpB)
  have hcoreCover : (π '' K)ᶜ ⊆ ⋃ i, U i := by
    intro x hx
    by_contra hxU
    obtain ⟨p, rfl⟩ := hsurj x
    exact hx ⟨p, hxU, rfl⟩
  have hUdisj : Pairwise (Disjoint on U) := by
    intro i j hij
    exact (hdisj hij).mono subset_closure subset_closure
  have hUsmall (i : Fin n) : diam (U i) < ε := by
    simpa only [diam_closure] using hsmall i
  refine ⟨K, hK, hKG, ?_⟩
  intro C _ hconn hdiam
  exact continuum_meets_core_of_small_open_cover U hopen hUdisj hcoreCover hUsmall hconn hdiam

/-- The topological consequences in generic-level-continua (ii) and the
countability and local-connectedness part of (iii), from the actual
finite-length and quotient-dust hypotheses. -/
theorem generic_level_topology_of_compact_quotient_dust
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (π : Y → X) (hπ : Continuous π) (hsurj : Function.Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x})) {G : Set Y} (hG : IsOpen G)
    {B : Set X} (hB : IsCompact B) (hTD : IsTotallyDisconnected B)
    (hdust : π '' Gᶜ ⊆ B) (hlength : (μH[1] : Measure Y) G < ∞) :
    HasFiniteLargeContinuumBound X ∧
      {C : Set X | (∃ x, C = connectedComponent x) ∧ C.Nontrivial}.Countable ∧
      ∀ C : Set X, IsCompact C → IsConnected C → LocallyConnectedSpace C := by
  have hbound := finite_large_continuum_bound_of_compact_quotient_dust
    π hπ hsurj hfiber hG hB hTD hdust hlength
  exact ⟨hbound, countable_nontrivial_connectedComponents hbound,
    fun _ hcompact hconn =>
      locallyConnected_subcontinuum_of_finite_large_continuum_bound hbound hcompact hconn⟩

end CircleDomainRigidity

end OAI
