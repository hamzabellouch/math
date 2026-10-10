import OAI.Analysis.CircleDomains.Rigidity.MatchedRealMaskData
import OAI.Analysis.CircleDomains.Topology.FiniteBalloonAvoidance

namespace OAI

/-! The common point set uses the full matched component family. The
single unused-code center may be omitted during local compression and
restored at the end, since a singleton has null scalar image. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 def commonPointPlane : Set ℂ :=
  {z | (z : Sphere) ∈ Gᶜ ∧ ∀ j : D.IndexedMatchedPair, (z : Sphere) ∉ j.val.1}

 theorem commonPointPlane_singletons
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {z : ℂ} (hz : z ∈ D.commonPointPlane) :
    connectedComponentIn Gᶜ (z : Sphere) = {(z : Sphere)} ∧
      ∃ p, D.targetFiber (z : Sphere) = {p} :=
  D.unindexed_components_singleton hG hinf hf hH hinf' hz.1 hz.2

variable {D} [Encodable D.IndexedMatchedPair]

 theorem MatchedRoundDisks.commonPoint_gap (E : D.MatchedRoundDisks)
    {z : ℂ} (hz : z ∈ D.commonPointPlane) (hz0 : z ≠ 0) (n : ℕ) :
    E.traceRadius n < ‖z-E.traceCenter n‖ := by
  by_cases hn : n ∈ Set.range (Encodable.encode : D.IndexedMatchedPair → ℕ)
  · obtain ⟨j,rfl⟩ := hn
    simp only [traceRadius,traceCenter,traceEnumeration_encode]
    apply lt_of_not_ge
    intro h
    exact hz.2 j (by rw [E.source_eq]; exact mem_image_of_mem _ (by simpa only [mem_closedBall,dist_eq_norm] using h))
  · simp only [traceRadius,traceCenter,traceEnumeration_missing _ _ hn,sub_zero]
    exact norm_pos_iff.mpr hz0

 theorem MatchedRoundDisks.commonPoint_prefix_avoidance (E : D.MatchedRoundDisks)
    {z : ℂ} (hz : z ∈ D.commonPointPlane) (hz0 : z ≠ 0) (N : ℕ) :
    ∃ (m : ℕ) (V : Set ℂ), IsOpen V ∧ z ∈ V ∧
      ∀ w ∈ V, ∀ j < N, traceBalloonRadius E.traceRadius m j ≤ ‖w-E.traceCenter j‖ :=
  exists_finite_balloon_avoidance (traceEnumeration_nonneg E.source_nonneg)
    (E.commonPoint_gap hz hz0) N

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
