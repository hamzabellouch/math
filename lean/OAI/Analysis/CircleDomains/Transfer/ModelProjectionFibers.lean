import OAI.Analysis.CircleDomains.Selection.ProjectionEndFibers
import OAI.Analysis.CircleDomains.Topology.CompactScalarModel

namespace OAI

/-! Fiber identification for the actual coefficient-extremal scalar model.
Only the already cited geometric inputs construct its matched exhaustion. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem projection_fiber (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {p : Sphere} (hp : p ∉ extendAtInfinity M.function '' G) :
    M.projection ⁻¹' {M.projection p} =
      connectedComponentIn (extendAtInfinity M.function '' G)ᶜ p := by
  obtain ⟨C, J, hstrict, hcover, hd, he, hb, hs⟩ := exists_matched_jordan_exhaustion
    hsard hsch hG hconn hinf M.conformal.1 M.conformal.bijOn.injOn rfl
  exact (inverse_projection_component_eq_fiber hG hTD M.conformal.1 M.conformal.bijOn.injOn
    M.projection_continuous M.projection_inverse M.projection_outside
    C J hstrict hcover hd he hb hs hp).symm

 theorem projection_surjective (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ) :
    Surjective M.projection := by
  obtain ⟨C, J, hstrict, hcover, hd, he, hb, hs⟩ := exists_matched_jordan_exhaustion
    hsard hsch hG hconn hinf M.conformal.1 M.conformal.bijOn.injOn rfl
  intro q
  by_cases hq : q ∈ G
  · exact ⟨extendAtInfinity M.function q, M.projection_inverse q hq⟩
  · obtain ⟨b, p, hp, hsource, htarget, _⟩ := corresponding_target_end_of_source hG
      M.conformal.1 M.conformal.bijOn.injOn C J hstrict hcover hd he hb hs hq
    refine ⟨p, ?_⟩
    have hmem : M.projection p ∈ connectedComponentIn Gᶜ q := by
      rw [hsource]
      apply mem_iInter.mpr
      intro n
      have hfront : ((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk (b n))) ⊆ G := by
        intro x hx
        apply (C n).subset
        have hh : x ∈ frontier (C n).carrier := by
          rw [SmoothJordanCore.carrier, frontier_closedJordanCore (C n).disk (C n).disjoint]
          exact mem_iUnion.mpr ⟨b n, hx⟩
        simpa only [(C n).isCompact.isClosed.closure_eq] using frontier_subset_closure hh
      apply inverse_projection_matched_cap hG M.projection_continuous
        M.projection_inverse M.projection_outside ((C n).disk (b n)) (J n (b n))
        hfront (hb n (b n)) (hs n (b n))
      exact mem_image_of_mem _ (mem_iInter.mp (htarget ▸ mem_connectedComponentIn hp) n)
    have hsingle : connectedComponentIn Gᶜ q = {q} :=
      (hTD _ (connectedComponentIn_subset _ _) isPreconnected_connectedComponentIn).eq_singleton_of_mem
        (mem_connectedComponentIn hq)
    simpa only [hsingle, mem_singleton_iff] using hmem

 theorem projection_closed (M : CompactScalarModel G u) : IsClosedMap M.projection :=
  M.projection_continuous.isClosedMap

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
