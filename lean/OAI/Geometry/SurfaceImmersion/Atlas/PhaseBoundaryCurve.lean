import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceCurveExterior
import OAI.Geometry.SurfaceImmersion.Geometry.CurveSecondTransition

namespace OAI

/-! Fixed compact boundary curves and their actual second-form fields.
The cutoff is chosen from the curve geometry, independently of any immersion. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes VelocityFrame NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

structure PhaseBoundaryCurve (B : SmoothingAtlas M) where
  index : B.centers
  phase : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base
  smooth : ContDiff ℝ ∞ phase
  inverse_smooth : ContDiff ℝ ∞ phase.symm
  carrier : Set M
  compact : IsCompact carrier
  source : carrier ⊆ ((chart (index : M)).trans phase).source
  active : ∀ p ∈ carrier, B.weight index p ≠ 0

namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c : PhaseBoundaryCurve B)

def coordinate (p : M) : SmallModes.Base := baseEquiv (c.phase (chart (c.index : M) p))

omit [CompactSpace M] in
lemma coordinate_continuous : ContinuousOn c.coordinate c.carrier :=
  baseEquiv.continuous.comp_continuousOn
    (((chart (c.index : M)).trans c.phase).continuousOn.mono c.source)

omit [CompactSpace M] in
lemma coordinate_compact : IsCompact (c.coordinate '' c.carrier) :=
  c.compact.image_of_continuousOn c.coordinate_continuous

lemma cutoff_exists : ∃ β : SmallModes.Base → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
    (∀ x ∈ c.coordinate '' c.carrier, β x = 1) ∧
    ∀ x ∈ tsupport β, baseEquiv.symm x ∈ c.phase.target ∧
      B.chartWeight c.index (c.phase.symm (baseEquiv.symm x)) ≠ 0 := by
  apply B.phase_curve_cutoff c.index c.phase c.inverse_smooth c.coordinate_compact
  · rintro x ⟨p,hp,rfl⟩
    have hs : chart (c.index : M) p ∈ c.phase.source := (c.source hp).2
    simpa only [coordinate,baseEquiv.symm_apply_apply] using c.phase.map_source hs
  · rintro x ⟨p,hp,rfl⟩
    have hs : chart (c.index : M) p ∈ c.phase.source := (c.source hp).2
    change B.chartWeight c.index (c.phase.symm (baseEquiv.symm (baseEquiv (c.phase (chart (c.index : M) p))))) ≠ 0
    rw [baseEquiv.symm_apply_apply,c.phase.left_inv hs,SmoothingAtlas.chartWeight,
      indicator_of_mem ((chart (c.index : M)).map_source (c.source hp).1),
      (chart (c.index : M)).left_inv (c.source hp).1]
    exact c.active p hp

def cutoff : SmallModes.Base → ℝ := Classical.choose c.cutoff_exists

lemma cutoff_properties : ContDiff ℝ ∞ c.cutoff ∧ HasCompactSupport c.cutoff ∧
    (∀ x ∈ c.coordinate '' c.carrier, c.cutoff x = 1) ∧
    ∀ x ∈ tsupport c.cutoff, baseEquiv.symm x ∈ c.phase.target ∧
      B.chartWeight c.index (c.phase.symm (baseEquiv.symm x)) ≠ 0 :=
  Classical.choose_spec c.cutoff_exists

def second (F : M → Space) (p : M) : Vec :=
  spaceCoordinates (B.phaseCurveSecondField c.index c.phase c.cutoff F
    (fun _ => dy) (fun _ => dy) p)

lemma second_smooth {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F) :
    ContMDiff planeModel 𝓘(ℝ,Vec) ∞ (c.second F) := by
  exact spaceCoordinates.contDiff.contMDiff.comp
    (B.phaseCurveSecondField_smooth c.index c.phase c.smooth c.inverse_smooth hF
      c.cutoff_properties.1 c.cutoff_properties.2.2.2 contDiff_const contDiff_const)

lemma second_eq (F : M → Space) {p : M} (hp : p ∈ c.carrier) :
    c.second F p = realSecondForm (B.phaseRealChartMap c.index c.phase.symm F)
      dy dy (c.coordinate p) := by
  apply B.phaseCurveSecondField_eq c.index c.phase c.cutoff F (fun _ => dy) (fun _ => dy)
    (c.source hp).1
  · exact B.outer_one c.index p (subset_tsupport _ (c.active p hp))
  · exact c.cutoff_properties.2.2.1 _ ⟨p,hp,rfl⟩

lemma second_transition (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    {p : M} (hp : p ∈ c.carrier)
    (hps : p ∈ (surfacePhaseChart (i : M) e).source) (hw : A.weight i p ≠ 0) :
    let T := surfacePhaseTransition (c.index : M) c.phase (i : M) e
    c.second F p = realSecondForm (A.phaseRealChartMap i e.symm F)
      (fderiv ℝ T (c.coordinate p) dy) (fderiv ℝ T (c.coordinate p) dy)
      (baseEquiv (e (chart (i : M) p))) := by
  have hpc : p ∈ (surfacePhaseChart (c.index : M) c.phase).source := c.source hp
  have hback : (surfacePhaseChart (c.index : M) c.phase).symm (c.coordinate p) = p :=
    (surfacePhaseChart (c.index : M) c.phase).left_inv hpc
  have hx : c.coordinate p ∈ (surfacePhaseTransition (c.index : M) c.phase (i : M) e).source := by
    refine ⟨(surfacePhaseChart (c.index : M) c.phase).map_source hpc,?_⟩
    change (surfacePhaseChart (c.index : M) c.phase).symm (c.coordinate p) ∈
      (surfacePhaseChart (i : M) e).source
    rwa [hback]
  have h := A.curveSecondField_transition B i c.index e c.phase he hi c.smooth c.inverse_smooth
    hF c.cutoff hx (by rw [hback]; exact c.active p hp) (by rwa [hback])
    (c.cutoff_properties.2.2.1 _ ⟨p,hp,rfl⟩)
  have ht : surfacePhaseTransition (c.index : M) c.phase (i : M) e (c.coordinate p) =
      baseEquiv (e (chart (i : M) p)) := by
    change (surfacePhaseChart (i : M) e)
      ((surfacePhaseChart (c.index : M) c.phase).symm (c.coordinate p)) = _
    rw [hback]
    rfl
  change spaceCoordinates (B.phaseCurveSecondField c.index c.phase c.cutoff F
    (fun _ => dy) (fun _ => dy)
    ((surfacePhaseChart (c.index : M) c.phase).symm (c.coordinate p))) =
    realSecondForm (A.phaseRealChartMap i e.symm F)
      (fderiv ℝ (surfacePhaseTransition (c.index : M) c.phase (i : M) e) (c.coordinate p) dy)
      (fderiv ℝ (surfacePhaseTransition (c.index : M) c.phase (i : M) e) (c.coordinate p) dy)
      (surfacePhaseTransition (c.index : M) c.phase (i : M) e (c.coordinate p)) at h
  rw [hback,ht] at h
  exact h

theorem exterior_preservation (A : SmoothingAtlas M)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (hB : ∀ p ∈ c.carrier, c.second F p ≠ 0)
    (havoid : ∀ p ∈ c.carrier, spaceCoordinates (n.vector p) ≠ -normalize (c.second F p)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W → ∀ b d : ℝ, 0 ≤ b → 0 ≤ d → b+d < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 d (W-V) →
      ∀ O : Set M, (∀ y ∈ O, V =ᶠ[𝓝 y] G) → ∀ p ∈ c.carrier ∩ closure O,
      A.projectedNormalField W n.vector p ≠ 0 ∧ c.second W p ≠ 0 ∧
      spaceCoordinates (A.unitProjectedNormalField W n.vector p) ≠ -normalize (c.second W p) := by
  obtain ⟨ρ,hρ,hpres⟩ := A.compact_surface_phase_exterior_preservation B hF n houter
    c.index c.phase c.smooth c.inverse_smooth c.compact c.source c.active
    (fun p hp => by simpa only [c.second_eq F hp,coordinate] using hB p hp)
    (fun p hp => by simpa only [c.second_eq F hp,coordinate] using havoid p hp)
  refine ⟨ρ,hρ,?_⟩
  intro G V W hG hV hW b d hb hd hbd hGF hWV O hext p hp
  simpa only [c.second_eq W hp.1,coordinate] using hpres G V W hG hV hW b d hb hd hbd hGF hWV O hext p hp

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
