import OAI.Geometry.SurfaceImmersion.Primitive.PhaseBoundaryProfile
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasJetCoordinateRelation
import OAI.Geometry.SurfaceImmersion.Primitive.LocalIntrinsicCrossing

namespace OAI

/-! The actual surface chart associated with a nonlinear phase. It is
independent of the correction atlas and supplies the chart transitions for later curves. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4
open SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

def surfacePhaseChart (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) :
    OpenPartialHomeomorph M SmallModes.Base :=
  ((FiniteOrderSmoothing.chart q).trans e).transHomeomorph baseEquiv.toHomeomorph

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseChart_apply (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (p : M) :
    surfacePhaseChart q e p = baseEquiv (e (FiniteOrderSmoothing.chart q p)) := rfl

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseChart_symm_apply (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (x : SmallModes.Base) :
    (surfacePhaseChart q e).symm x =
      (FiniteOrderSmoothing.chart q).symm (e.symm (baseEquiv.symm x)) := rfl

lemma surfacePhaseChart_smooth (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) :
    ContMDiffOn planeModel 𝓘(ℝ,SmallModes.Base) ∞ (surfacePhaseChart q e)
      (surfacePhaseChart q e).source := by
  exact (baseEquiv.contDiff.comp he).contMDiff.comp_contMDiffOn
    ((FiniteOrderSmoothing.chart_smooth q).mono (fun _ hx => hx.1))

lemma surfacePhaseChart_symm_smooth (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) :
    ContMDiffOn 𝓘(ℝ,SmallModes.Base) planeModel ∞ (surfacePhaseChart q e).symm
      (surfacePhaseChart q e).target := by
  exact (FiniteOrderSmoothing.chart_symm_smooth q).comp
    (hi.comp baseEquiv.symm.contDiff).contMDiff.contMDiffOn (fun _ hx => hx.2)

def surfacePhaseTransition (p : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (q : M)
    (f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) :
    OpenPartialHomeomorph SmallModes.Base SmallModes.Base :=
  (surfacePhaseChart p e).symm.trans (surfacePhaseChart q f)

lemma surfacePhaseTransition_smooth (p : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) (q : M)
    (f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (surfacePhaseTransition p e q f) (surfacePhaseTransition p e q f).source := by
  apply ContMDiffOn.contDiffOn
  exact (surfacePhaseChart_smooth q f hf).comp
    ((surfacePhaseChart_symm_smooth p e hi).mono (fun _ hx => hx.1)) (fun _ hx => hx.2)

lemma surfacePhaseTransition_det_ne (p : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm) (q : M)
    (f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hf : ContDiff ℝ ∞ f) (hfi : ContDiff ℝ ∞ f.symm)
    {x : SmallModes.Base} (hx : x ∈ (surfacePhaseTransition p e q f).source) :
    RealModes.coordDet (fderiv ℝ (surfacePhaseTransition p e q f) x) ≠ 0 := by
  let T := surfacePhaseTransition p e q f
  have hs : ContDiffOn ℝ ∞ T T.source := surfacePhaseTransition_smooth p e hi q f hf
  have ht : ContDiffOn ℝ ∞ T.symm T.target := by
    change ContDiffOn ℝ ∞ (surfacePhaseTransition q f p e) (surfacePhaseTransition q f p e).source
    exact surfacePhaseTransition_smooth q f hfi p e he
  exact RealModes.coordDet_fderiv_ne_zero_of_local_inverse T.open_source T.open_target
    hs ht T.mapsTo (fun y hy => T.left_inv hy) hx

def surfacePhaseMap (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (F : M → Space) :
    SmallModes.Base → NormalFrame.Vec := spaceCoordinates ∘ F ∘ (surfacePhaseChart q e).symm

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseMap_transition_germ (p q : M)
    (e f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (F : M → Space)
    {x : SmallModes.Base} (hx : x ∈ (surfacePhaseTransition p e q f).source) :
    surfacePhaseMap p e F =ᶠ[𝓝 x]
      surfacePhaseMap q f F ∘ surfacePhaseTransition p e q f := by
  filter_upwards [(surfacePhaseTransition p e q f).open_source.mem_nhds hx] with y hy
  change spaceCoordinates (F ((surfacePhaseChart p e).symm y)) =
    spaceCoordinates (F ((surfacePhaseChart q f).symm
      ((surfacePhaseChart q f) ((surfacePhaseChart p e).symm y))))
  have hyj : (surfacePhaseChart p e).symm y ∈ (surfacePhaseChart q f).source := hy.2
  rw [(surfacePhaseChart q f).left_inv hyj]

end ClosedSurfaceR4

end

end OAI
