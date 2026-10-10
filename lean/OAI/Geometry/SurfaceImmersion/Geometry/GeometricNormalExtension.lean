import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceCurveNormalGluing
import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceBoundaryMatching

namespace OAI

/-! Complete the global preferred-normal construction from the original
boundary crossing data and the local normal produced by the exact primitive. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes NormalFrame VelocityFrame GeometryPreservation
variable {M κ : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [Fintype κ]
namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

theorem geometric_normal_extension
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (curves : κ → PhaseBoundaryCurve B)
    (hold : ∀ k p, p ∈ (curves k).carrier → (curves k).second F p ≠ 0 ∧
      spaceCoordinates (n.vector p) ≠ -normalize ((curves k).second F p))
    (i : A.centers) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {D : Set M} (hD : IsOpen D) (hDr : interior (closure D) = D)
    (hDs : closure D ⊆ (chart (i : M)).source)
    (hDe : MapsTo (chart (i : M)) (closure D) e.source)
    (hDw : ∀ p ∈ closure D, A.weight i p ≠ 0)
    (E : Set M) (hE : E.Finite) (hEf : Disjoint E (frontier D))
    (v : κ → SmallModes.Base → SmallModes.Base) (hv : ∀ k, Continuous (v k))
    (hvector : ∀ k p, p ∈ (curves k).carrier → p ∈ closure D →
      v k (baseEquiv (e (chart (i : M) p))) =
        fderiv ℝ (surfacePhaseTransition ((curves k).index : M) (curves k).phase (i : M) e)
          ((curves k).coordinate p) dy)
    (hboundary : ∀ p ∈ frontier D,
      realSecondForm (A.phaseRealChartMap i e.symm F) dy dy
        (baseEquiv (e (chart (i : M) p))) ≠ 0 ∧
      spaceCoordinates (n.vector p) ≠ -normalize (realSecondForm (A.phaseRealChartMap i e.symm F)
        dy dy (baseEquiv (e (chart (i : M) p)))))
    (hpositive : ∀ k p, p ∈ (curves k).carrier → p ∈ frontier D →
      0 < (curves k).second F p ⬝ᵥ spaceCoordinates (n.vector p))
    (hcross : ∀ k p, p ∈ (curves k).carrier → p ∈ frontier D →
      let q := baseEquiv (e (chart (i : M) p))
      let H := A.phaseRealChartMap i e.symm F
      0 < orderedCrossing H dy (v k q) q
        (coordinateGaussianCurvature (realMetric H dx dx) (realMetric H dx dy) (realMetric H dy dy) q)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ∀ h : SmoothMetric M, IsSmoothIsometricImmersion M h W →
      ∀ b d : ℝ, 0 ≤ b → 0 ≤ d → b+d < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 d (W-V) →
      (∀ p ∉ closure D, V =ᶠ[𝓝 p] G) →
      ∀ z : ℝ, ∀ U₀ : Set SmallModes.Base, IsOpen U₀ → ∀ ν : SmallModes.Base → Vec,
      ContDiffOn ℝ ∞ ν U₀ →
      (∀ x ∈ U₀, ν x ⬝ᵥ ν x = 1) →
      (∀ x ∈ U₀, ∀ w : SmallModes.Base,
        SmallModes.coordDeriv w (A.phaseRealChartMap i e.symm W) x ⬝ᵥ ν x = 0) →
      MapsTo (fun p => baseEquiv (e (chart (i : M) p))) (closure D) U₀ →
      (∀ p ∈ frontier D, ν (baseEquiv (e (chart (i : M) p))) =
        profilePreferred (realBoundaryProfile (A.phaseRealChartMap i e.symm W) z
          (baseEquiv (e (chart (i : M) p))))) →
      (∀ k p, p ∈ (curves k).carrier → p ∈ D →
        let q := baseEquiv (e (chart (i : M) p))
        realSecondForm (A.phaseRealChartMap i e.symm W) (v k q) (v k q) q ≠ 0 ∧
        ν q ≠ -normalize (realSecondForm (A.phaseRealChartMap i e.symm W) (v k q) (v k q) q)) →
      ∃ N : PreferredNormal W,
        (∀ k p, p ∈ (curves k).carrier → (curves k).second W p ≠ 0 ∧
          spaceCoordinates (N.vector p) ≠ -normalize ((curves k).second W p)) ∧
        ∀ p ∈ E, (p ∈ D → N.vector p = A.phaseNormalLift i e ν p) ∧
          (p ∉ D → N.vector p = A.unitProjectedNormalField W n.vector p) := by
  classical
  have hsource : closure D ⊆ ((chart (i : M)).trans e).source :=
    fun p hp => ⟨hDs hp,hDe hp⟩
  have hread {h : SmoothMetric M} {W : M → Space} (hW : IsSmoothIsometricImmersion M h W)
      (k : κ) (p : M) (hp : p ∈ (curves k).carrier) (hpD : p ∈ closure D) :
      (curves k).second W p =
        realSecondForm (A.phaseRealChartMap i e.symm W)
          (v k (baseEquiv (e (chart (i : M) p))))
          (v k (baseEquiv (e (chart (i : M) p))))
          (baseEquiv (e (chart (i : M) p))) := by
    rw [(curves k).second_transition A i e he hi hW hp (hsource hpD) (hDw p hpD),
      hvector k p hp hpD]
  obtain ⟨r,hr,hglue⟩ := A.finite_curve_disk_normal B hF n houter curves hold i e he hi
    hD hDr hDs hDe hDw E hE hEf
  obtain ⟨a,ha,hanti⟩ := A.compact_surface_phase_exterior_preservation A hF n houter i e he hi
    (isClosed_frontier.isCompact) (fun p hp => hsource (frontier_subset_closure hp))
    (fun p hp => hDw p (frontier_subset_closure hp))
    (fun p hp => (hboundary p hp).1) (fun p hp => (hboundary p hp).2)
  have hpair (k : κ) := A.compact_surface_boundary_matching hF n houter i e he hi
    ((curves k).compact.inter_right isClosed_frontier)
    (fun p hp => hsource (frontier_subset_closure hp.2))
    (fun p hp => hDw p (frontier_subset_closure hp.2)) (v k) (hv k)
    (fun p hp => (hboundary p hp.2).1) (fun p hp => (hboundary p hp.2).2)
    (fun p hp => by dsimp only; rw [← hread hF k p hp.1 (frontier_subset_closure hp.2)]; exact hpositive k p hp.1 hp.2)
    (fun p hp => hcross k p hp.1 hp.2)
  choose t ht hpair' using hpair
  obtain ⟨s,hs,_,hst⟩ := finite_positive_threshold t ht
  refine ⟨min r (min a s),lt_min hr (lt_min ha hs),?_⟩
  intro G V W hG hV h hW b d hb hd hbd hGF hWV hext z U₀ hU₀ ν hν hunit hnormal hDU hcanonical hlocal
  have hbd_r := hbd.trans_le (min_le_left r (min a s))
  have hbd_a := hbd.trans_le ((min_le_right r (min a s)).trans (min_le_left a s))
  have hbd_s := hbd.trans_le ((min_le_right r (min a s)).trans (min_le_right a s))
  have hclosure (p : M) (hp : p ∈ frontier D) : p ∈ closure (closure D)ᶜ := by
    rw [closure_compl,hDr]
    exact hD.frontier_eq ▸ hp |>.2
  apply hglue G V W hG hV h hW b d hb hd hbd_r hGF hWV hext U₀ hU₀ ν hν hunit hnormal hDU
  · intro p hp
    rw [hcanonical p hp,profilePreferred_real]
    exact (hanti G V W hG hV hW.1 b d hb hd hbd_a hGF hWV (closure D)ᶜ hext p
      ⟨hp,hclosure p hp⟩).2.2
  · intro k p hp hpD
    rw [hread hW k p hp (subset_closure hpD)]
    exact hlocal k p hp hpD
  · intro k p hp hpD
    rw [hread hW k p hp (frontier_subset_closure hpD),hcanonical p hpD]
    have hh := hpair' k G V W hG hV hW.1 b d hb hd (hbd_s.trans_le (hst k))
      hGF hWV (closure D)ᶜ hext p ⟨⟨hp,hpD⟩,hclosure p hpD⟩ z
    exact ⟨hh.2,hh.1⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
