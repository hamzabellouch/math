import OAI.Geometry.SurfaceImmersion.Atlas.PhaseBoundaryCurve
import OAI.Geometry.SurfaceImmersion.Primitive.CrossingSafeNormalGluing

namespace OAI

/-! The global normal step for actual surface curves. A single smallness
threshold handles every exterior curve and the whole exterior normal field. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes NormalFrame VelocityFrame
variable {M κ : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [Fintype κ]
namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

theorem finite_curve_disk_normal
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
    (E : Set M) (hE : E.Finite) (hEf : Disjoint E (frontier D)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ∀ h : SmoothMetric M, IsSmoothIsometricImmersion M h W →
      ∀ b d : ℝ, 0 ≤ b → 0 ≤ d → b+d < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 d (W-V) →
      (∀ p ∉ closure D, V =ᶠ[𝓝 p] G) →
      ∀ U₀ : Set SmallModes.Base, IsOpen U₀ → ∀ ν : SmallModes.Base → Vec,
      ContDiffOn ℝ ∞ ν U₀ →
      (∀ x ∈ U₀, ν x ⬝ᵥ ν x = 1) →
      (∀ x ∈ U₀, ∀ v : SmallModes.Base,
        SmallModes.coordDeriv v (A.phaseRealChartMap i e.symm W) x ⬝ᵥ ν x = 0) →
      MapsTo (fun p => baseEquiv (e (chart (i : M) p))) (closure D) U₀ →
      (∀ p ∈ frontier D, spaceCoordinates (A.unitProjectedNormalField W n.vector p) ≠
        -ν (baseEquiv (e (chart (i : M) p)))) →
      (∀ k p, p ∈ (curves k).carrier → p ∈ D →
        (curves k).second W p ≠ 0 ∧
        ν (baseEquiv (e (chart (i : M) p))) ≠ -normalize ((curves k).second W p)) →
      (∀ k p, p ∈ (curves k).carrier → p ∈ frontier D →
        0 < (curves k).second W p ⬝ᵥ ν (baseEquiv (e (chart (i : M) p))) ∧
        0 < (curves k).second W p ⬝ᵥ spaceCoordinates (A.unitProjectedNormalField W n.vector p)) →
      ∃ N : PreferredNormal W,
        (∀ k p, p ∈ (curves k).carrier → (curves k).second W p ≠ 0 ∧
          spaceCoordinates (N.vector p) ≠ -normalize ((curves k).second W p)) ∧
        ∀ p ∈ E, (p ∈ D → N.vector p = A.phaseNormalLift i e ν p) ∧
          (p ∉ D → N.vector p = A.unitProjectedNormalField W n.vector p) := by
  classical
  choose r hr hpres using fun k => (curves k).exterior_preservation A hF n houter
    (fun p hp => (hold k p hp).1) (fun p hp => (hold k p hp).2)
  obtain ⟨s,hs,_,hsr⟩ := finite_positive_threshold r hr
  obtain ⟨t,ht,hproj⟩ := A.exterior_projected_normal_close_closure hF.1 n.smooth n.unit n.normal
    (fun j p hp => A.planeRead_gram_of_immersion hF.1
      (IsSmoothIsometricImmersion.mfderiv_injective hF) houter j hp) zero_lt_one
  refine ⟨min s t,lt_min hs ht,?_⟩
  intro G V W hG hV h hW b d hb hd hbd hGF hWV hext U₀ hU₀ ν hν hunit hnormal hDU hanti hin hpair
  have hclosure (p : M) (hp : p ∉ D) : p ∈ closure (closure D)ᶜ := by
    rwa [closure_compl,hDr]
  have hcurve (k : κ) (p : M) (hp : p ∈ (curves k).carrier) (hpD : p ∉ D) :=
    hpres k G V W hG hV hW.1 b d hb hd
      ((hbd.trans_le (min_le_left _ _)).trans_le (hsr k)) hGF hWV (closure D)ᶜ
      hext p ⟨hp,hclosure p hpD⟩
  have hpn (p : M) (hpD : p ∉ D) : A.projectedNormalField W n.vector p ≠ 0 :=
    (hproj G V W hG hV hW.1 b d hb hd (hbd.trans_le (min_le_right _ _)) hGF hWV
      (closure D)ᶜ hext p (hclosure p hpD)).1
  obtain ⟨N,havoid,hmatch⟩ := A.crossing_safe_phase_normal_gluing i hW.1
    (IsSmoothIsometricImmersion.mfderiv_injective hW) n.smooth houter e he hi hD E hE hEf
    hU₀ hν hunit hnormal hDs hDe hDU hDw hpn hanti
    (fun k => (curves k).carrier) (fun k => (curves k).compact.isClosed)
    (fun k => (curves k).second W) (fun k => ((curves k).second_smooth hW).continuous)
    (fun k p hp hpD => (hin k p hp hpD).2)
    (fun k p hp hpD => (hcurve k p hp (fun hpd => hpD (subset_closure hpd))).2.2) hpair
  refine ⟨N,?_,hmatch⟩
  intro k p hp
  refine ⟨?_,havoid k p hp⟩
  by_cases hpD : p ∈ D
  · exact (hin k p hp hpD).1
  · exact (hcurve k p hp hpD).2.1

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
