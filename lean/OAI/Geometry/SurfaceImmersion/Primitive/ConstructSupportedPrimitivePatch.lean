import OAI.Geometry.SurfaceImmersion.Primitive.SupportedPrimitivePatch
import OAI.Geometry.SurfaceImmersion.Primitive.AdaptedPrimitiveGeometry

namespace OAI

/-! A supported primitive patch is constructed from the actual immersion,
its preferred normal, metric convexity and the original boundary condition. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

theorem construct_supported_primitive_patch (j : B.centers)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {D : Set M} (hD : IsOpen D) (hqD : (j : M) ∈ D)
    (hDs : closure D ⊆ (surfacePhaseChart (j : M) e).source)
    {Ω : Set Base} (hΩ : IsOpen Ω)
    (hDΩ : (surfacePhaseChart (j : M) e) '' closure D ⊆ Ω)
    (hΩe : Ω ⊆ (surfacePhaseChart (j : M) e).target)
    (hactive : ∀ x ∈ Ω, B.weight j ((surfacePhaseChart (j : M) e).symm x) ≠ 0)
    {localPhase : Base → ℝ} (hlocalPhase : ContDiff ℝ ∞ localPhase)
    (hphase : ∀ x, (JetPolynomial.realPhaseChart e x).1 = localPhase x)
    (hconvex : ∀ x ∈ Ω, ∀ v : Base, v ≠ 0 →
      0 < coordinateMetricHessian (coordinateMetric g (j : M)) localPhase
        (coordinateChart (j : M) ((surfacePhaseChart (j : M) e).symm x)) v v)
    (hboundary : ∀ x ∈ frontier ((surfacePhaseChart (j : M) e) '' D),
      realSecondForm (B.phaseRealChartMap j e.symm F) dy dy x ≠ 0 ∧
      normalize (realSecondForm (B.phaseRealChartMap j e.symm F) dy dy x) ≠ -n.inPhase (j : M) e x)
    {amp phi : M → ℝ} (hamp : ContMDiff planeModel 𝓘(ℝ) ∞ amp)
    (hamp0 : ∀ p, 0 ≤ amp p) (hamppos : ∀ p, 0 < amp p ↔ p ∈ D)
    (hphi : ∀ p ∈ D, phi =ᶠ[𝓝 p] (fun q => (e (chart (j : M) q)) 0)) :
    ∃ (A : SmoothingAtlas M) (i : A.centers)
      (f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base),
      (i : M) = (j : M) ∧ (∀ x, f x = e x) ∧ (∀ x, f.symm x = e.symm x) ∧
      Nonempty (SupportedPrimitivePatch A i f F amp phi D) := by
  obtain ⟨V,A,i,f,U,hV,hVc,hDV,hVΩ,hij,hfe,hfi,hfs,hfis,hw,houter,hcover,hsource,hDf,
      hU,hVU,_hUΩ,hn,hI,hN,hH,hb⟩ := B.adapted_primitive_geometry j hF n e he hi
    hD hqD hDs hΩ hDΩ hΩe hactive hlocalPhase hphase hconvex hboundary
  have hE : (surfacePhaseChart (i : M) f : M → Base) = surfacePhaseChart (j : M) e := by
    funext p
    simp only [surfacePhaseChart_apply,hij,hfe]
  have hph : (fun q => (f (chart (i : M) q)) 0) = (fun q => (e (chart (j : M) q)) 0) := by
    funext p
    rw [hij,hfe]
  refine ⟨A,i,f,hij,hfe,hfi,?_⟩
  apply A.supported_primitive_patch i f hfs hfis houter hcover hDf
    (fun p hp => (hw p hp).ne') hamp hamp0 hamppos
    (by simpa only [hph] using hphi) hV hVc
    (by simpa only [hE] using hDV) hsource hU hVU hn hI hN hH
  simpa only [hE] using hb

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
