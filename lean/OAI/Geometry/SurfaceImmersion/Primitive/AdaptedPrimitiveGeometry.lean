import OAI.Geometry.SurfaceImmersion.Primitive.AdaptedPhasePrimitiveAtlas
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveOuterGeometry
import OAI.Geometry.SurfaceImmersion.Whitney.PrimitiveBoundaryCollar
import OAI.Geometry.SurfaceImmersion.Atlas.CrossAtlasOuterGeometry
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseExteriorDomain

namespace OAI

/-! Construct the entire analytic chart neighborhood from the actual
surface metric, preferred normal and primitive boundary. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

theorem adapted_primitive_geometry (j : B.centers)
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
    {phi : Base → ℝ} (hphi : ContDiff ℝ ∞ phi)
    (hphase : ∀ x, (JetPolynomial.realPhaseChart e x).1 = phi x)
    (hconvex : ∀ x ∈ Ω, ∀ v : Base, v ≠ 0 →
      0 < coordinateMetricHessian (coordinateMetric g (j : M)) phi
        (coordinateChart (j : M) ((surfacePhaseChart (j : M) e).symm x)) v v)
    (hboundary : ∀ x ∈ frontier ((surfacePhaseChart (j : M) e) '' D),
      realSecondForm (B.phaseRealChartMap j e.symm F) dy dy x ≠ 0 ∧
      normalize (realSecondForm (B.phaseRealChartMap j e.symm F) dy dy x) ≠ -n.inPhase (j : M) e x) :
    ∃ (V : Set Base) (A : SmoothingAtlas M) (i : A.centers)
      (f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (U : Set Base),
      IsOpen V ∧ IsCompact (closure V) ∧
      (surfacePhaseChart (j : M) e) '' closure D ⊆ V ∧ closure V ⊆ Ω ∧
      (i : M) = (j : M) ∧ (∀ x, f x = e x) ∧ (∀ x, f.symm x = e.symm x) ∧
      ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ f.symm ∧
      (∀ p ∈ closure D, 0 < A.weight i p) ∧
      (∀ k p, p ∈ tsupport (A.weight k) → A.outer k =ᶠ[𝓝 p] (fun _ => 1)) ∧
      (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ f.source ∧
      MapsTo f f.source (baseEquiv ⁻¹' V) ∧
      closure D ⊆ (surfacePhaseChart (i : M) f).source ∧
      IsOpen U ∧ closure V ⊆ U ∧ U ⊆ Ω ∧
      ContDiffOn ℝ ∞ (n.inPhase (j : M) e) U ∧
      (∀ x ∈ U, Function.Injective (fderiv ℝ (A.phaseRealChartMap i f.symm F) x)) ∧
      (∀ x ∈ U, coordDeriv dx (A.phaseRealChartMap i f.symm F) x ⬝ᵥ n.inPhase (j : M) e x = 0 ∧
        coordDeriv dy (A.phaseRealChartMap i f.symm F) x ⬝ᵥ n.inPhase (j : M) e x = 0 ∧
        n.inPhase (j : M) e x ⬝ᵥ n.inPhase (j : M) e x = 1) ∧
      (∀ x ∈ U, 0 < coordinateMetricHessian
        (inducedCoordinateMetric (A.phaseRealChartMap i f.symm F)) Prod.fst x dy dy) ∧
      ∀ x ∈ closure V \ ((surfacePhaseChart (j : M) e) '' D),
        realSecondForm (A.phaseRealChartMap i f.symm F) dy dy x ≠ 0 ∧
        normalize (realSecondForm (A.phaseRealChartMap i f.symm F) dy dy x) ≠ -n.inPhase (j : M) e x := by
  let E := surfacePhaseChart (j : M) e
  have hDc : IsCompact (closure D) := isClosed_closure.isCompact
  obtain ⟨hED,hEDcl,_hEDfront,hEDc⟩ := compact_phase_disk_geometry E hD hDc hDs
  have hEDΩ : closure (E '' D) ⊆ Ω := by rwa [hEDcl]
  have hgram : ∀ x ∈ Ω, NormalFrame.gramDet
      (coordDeriv dx (B.phaseRealChartMap j e.symm F) x)
      (coordDeriv dy (B.phaseRealChartMap j e.symm F) x) ≠ 0 := by
    intro x hx
    have hh := B.phase_gram_at_source j e he hi hF
      (E.map_target (hΩe hx)) (hactive x hx)
    change NormalFrame.gramDet _ _ ≠ 0 at hh
    have heq := E.right_inv (hΩe hx)
    change baseEquiv (e (chart (j : M) (E.symm x))) = x at heq
    rwa [heq] at hh
  obtain ⟨V,hV,hVc,hDV,hVΩ,hzero,_hcross⟩ := GeometryPreservation.primitive_boundary_collar
    (B.phaseRealChartMap_smooth j hi hF.1) hΩ hED hEDc hEDΩ hgram
    ((n.inPhase_smooth (j : M) e hi).mono hΩe) hboundary
    (fun _ : Fin 0 => (∅ : Set Base)) (fun _ => isClosed_empty)
    (fun _ : Fin 0 => (fun _ : Base => (0 : Base))) (fun _ => contDiff_const)
    (fun i => Fin.elim0 i)
  have hDV' : E '' closure D ⊆ V := by rwa [← hEDcl]
  obtain ⟨A,i,f,hij,hfe,hfi,hfs,hfis,hw,houter,hcover,hsource,hDf,hplateau⟩ :=
    adapted_phase_primitive_atlas (j : M) e he hi hDc (subset_closure hqD) hDs hV hVc hDV'
      (hVΩ.trans hΩe)
  have hΩA : Ω ⊆ (surfacePhaseChart (i : M) e).target := by rwa [hij]
  have hpA : ∀ x ∈ closure V,
      A.outer i =ᶠ[𝓝 ((surfacePhaseChart (i : M) e).symm x)] (fun _ => 1) := by
    simpa only [hij] using hplateau
  have hcvA : ∀ x ∈ Ω, ∀ v : Base, v ≠ 0 →
      0 < coordinateMetricHessian (coordinateMetric g (i : M)) phi
        (coordinateChart (i : M) ((surfacePhaseChart (i : M) e).symm x)) v v := by
    simpa only [hij] using hconvex
  obtain ⟨U,hU,hVU,hUΩ,hn,hI,hN,hH⟩ := A.primitive_outer_geometry i hF n e he hi
    hphi hphase hΩ hVΩ hΩA hpA hcvA
  have hm : A.phaseRealChartMap i f.symm F = A.phaseRealChartMap i e.symm F := by
    rw [show (f.symm : JetPolynomial.Base → JetPolynomial.Base) = e.symm from funext hfi]
  have hn' : n.inPhase (i : M) e = n.inPhase (j : M) e := by rw [hij]
  refine ⟨V,A,i,f,U,hV,hVc,hDV',hVΩ,hij,hfe,hfi,hfs,hfis,hw,houter,hcover,hsource,hDf,
    hU,hVU,hUΩ,?_,?_,?_,?_,?_⟩
  · rwa [hn'] at hn
  · rwa [hm]
  · rw [hm]
    simpa only [hn'] using hN
  · rwa [hm]
  · intro x hx
    rw [hm,A.phase_second_of_common_outer B i j hij e F (hΩe (hVΩ hx.1))
      (hplateau x hx.1) (hactive x (hVΩ hx.1)) dy dy]
    exact hzero x hx

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
