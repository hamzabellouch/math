import OAI.Geometry.SurfaceImmersion.Atlas.PhaseBoundaryCurve
import OAI.Geometry.SurfaceImmersion.Geometry.PreferredNormalGluing

namespace OAI

/-! Pull the actual global preferred normal into the primitive's phase
coordinates, preserving smoothness, unit length and orthogonality. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates SmallModes RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace PreferredNormal
variable {F : M → Space} (n : PreferredNormal F)

omit [IsManifold planeModel ∞ M] in
lemma pullback_normal_at (hF : ContMDiff planeModel spaceModel ∞ F)
    {u : Base → M} {x : Base} (hu : ContMDiffAt 𝓘(ℝ,Base) planeModel ∞ u x) (v : Base) :
    coordDeriv v (spaceCoordinates ∘ F ∘ u) x ⬝ᵥ spaceCoordinates (n.vector (u x)) = 0 := by
  have hF' : ContMDiff planeModel 𝓘(ℝ,NormalFrame.Vec) ∞ (spaceCoordinates ∘ F) :=
    spaceCoordinates.contDiff.contMDiff.comp hF
  change fderiv ℝ ((spaceCoordinates ∘ F) ∘ u) x v ⬝ᵥ _ = 0
  rw [← mfderiv_eq_fderiv,mfderiv_comp x (hF'.mdifferentiable (by simp)).mdifferentiableAt
    (hu.mdifferentiableAt (by simp))]
  rw [mfderiv_comp (u x)
    ((spaceCoordinates.contDiff (n := (∞ : ℕ∞ω))).contMDiff.mdifferentiable (by simp)).mdifferentiableAt
    (hF.mdifferentiable (by simp)).mdifferentiableAt,
    mfderiv_eq_fderiv,spaceCoordinates.fderiv]
  let vx : TangentSpace 𝓘(ℝ,Base) x := v
  let w : TangentSpace planeModel (u x) := mfderiv 𝓘(ℝ,Base) planeModel u x vx
  change spaceCoordinates (mfderiv planeModel spaceModel F (u x) w) ⬝ᵥ
    spaceCoordinates (n.vector (u x)) = 0
  exact (spaceCoordinates_dot _ _).trans (n.normal _ w)

def inPhase (q : M) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) :
    Base → NormalFrame.Vec := spaceCoordinates ∘ n.vector ∘ (surfacePhaseChart q e).symm

lemma inPhase_smooth (q : M) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) :
    ContDiffOn ℝ ∞ (n.inPhase q e) (surfacePhaseChart q e).target :=
  (spaceCoordinates.contDiff.contMDiff.comp n.smooth |>.comp_contMDiffOn
    (surfacePhaseChart_symm_smooth q e hi)).contDiffOn

omit [IsManifold planeModel ∞ M] in
lemma inPhase_unit (q : M) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (x : Base) : n.inPhase q e x ⬝ᵥ n.inPhase q e x = 1 := by
  change spaceCoordinates (n.vector _) ⬝ᵥ spaceCoordinates (n.vector _) = 1
  rw [spaceCoordinates_dot,real_inner_self_eq_norm_sq,n.unit]
  norm_num

lemma inPhase_normal (hF : ContMDiff planeModel spaceModel ∞ F)
    (q : M) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {x : Base} (hx : x ∈ (surfacePhaseChart q e).target)
    (v : Base) : coordDeriv v (surfacePhaseMap q e F) x ⬝ᵥ n.inPhase q e x = 0 := by
  exact n.pullback_normal_at hF
    ((surfacePhaseChart_symm_smooth q e hi x hx).contMDiffAt
      ((surfacePhaseChart q e).open_target.mem_nhds hx)) v

end PreferredNormal
namespace FiniteOrderSmoothing.SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma preferred_normal_in_phase (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (n : PreferredNormal F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {x : Base} (hx : x ∈ (surfacePhaseChart (i : M) e).target)
    (hw : A.weight i ((surfacePhaseChart (i : M) e).symm x) ≠ 0) (v : Base) :
    coordDeriv v (A.phaseRealChartMap i e.symm F) x ⬝ᵥ n.inPhase (i : M) e x = 0 := by
  have he := A.phaseRealChartMap_surface_germ i e F hx hw
  rw [coordDeriv,he.fderiv_eq]
  exact n.inPhase_normal hF (i : M) e hi hx v

end FiniteOrderSmoothing.SmoothingAtlas
end ClosedSurfaceR4

end

end OAI
