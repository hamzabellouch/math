import OAI.Geometry.SurfaceImmersion.Atlas.PhaseTransitionVectors

namespace OAI

/-! Chain identities for the actual nonlinear phase charts. They transport
both directions of an ordered crossing through a third chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseTransition_apply (q r : M)
    (e f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) {p : M}
    (hp : p ∈ (surfacePhaseChart q e).source) :
    surfacePhaseTransition q e r f (surfacePhaseChart q e p) = surfacePhaseChart r f p := by
  change (surfacePhaseChart r f) ((surfacePhaseChart q e).symm (surfacePhaseChart q e p)) = _
  rw [(surfacePhaseChart q e).left_inv hp]

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseTransition_source (q r : M)
    (e f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) {p : M}
    (hp : p ∈ (surfacePhaseChart q e).source) (hr : p ∈ (surfacePhaseChart r f).source) :
    surfacePhaseChart q e p ∈ (surfacePhaseTransition q e r f).source := by
  refine ⟨(surfacePhaseChart q e).map_source hp,?_⟩
  change (surfacePhaseChart q e).symm (surfacePhaseChart q e p) ∈ (surfacePhaseChart r f).source
  rwa [(surfacePhaseChart q e).left_inv hp]

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseTransition_cocycle_germ (q₁ q₂ q₃ : M)
    (e₁ e₂ e₃ : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {p : M} (h₁ : p ∈ (surfacePhaseChart q₁ e₁).source)
    (h₂ : p ∈ (surfacePhaseChart q₂ e₂).source)
    (h₃ : p ∈ (surfacePhaseChart q₃ e₃).source) :
    surfacePhaseTransition q₂ e₂ q₃ e₃ ∘ surfacePhaseTransition q₁ e₁ q₂ e₂ =ᶠ[𝓝 (surfacePhaseChart q₁ e₁ p)] surfacePhaseTransition q₁ e₁ q₃ e₃ := by
  have h₁₂ := surfacePhaseTransition_source q₁ q₂ e₁ e₂ h₁ h₂
  have h₁₃ := surfacePhaseTransition_source q₁ q₃ e₁ e₃ h₁ h₃
  filter_upwards [(surfacePhaseTransition q₁ e₁ q₂ e₂).open_source.mem_nhds h₁₂,
    (surfacePhaseTransition q₁ e₁ q₃ e₃).open_source.mem_nhds h₁₃] with x hx _
  have hxs : (surfacePhaseChart q₁ e₁).symm x ∈ (surfacePhaseChart q₂ e₂).source := hx.2
  change (surfacePhaseChart q₃ e₃) ((surfacePhaseChart q₂ e₂).symm
    ((surfacePhaseChart q₂ e₂) ((surfacePhaseChart q₁ e₁).symm x))) = _
  rw [(surfacePhaseChart q₂ e₂).left_inv hxs]
  rfl

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseTransition_self_germ (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {x : SmallModes.Base} (hx : x ∈ (surfacePhaseChart q e).target) :
    surfacePhaseTransition q e q e =ᶠ[𝓝 x] id := by
  filter_upwards [(surfacePhaseChart q e).open_target.mem_nhds hx] with y hy
  exact (surfacePhaseChart q e).right_inv hy

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseTransition_self_fderiv (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {x : SmallModes.Base} (hx : x ∈ (surfacePhaseChart q e).target) :
    fderiv ℝ (surfacePhaseTransition q e q e) x = ContinuousLinearMap.id ℝ SmallModes.Base := by
  rw [(surfacePhaseTransition_self_germ q e hx).fderiv_eq,fderiv_id]

lemma surfacePhaseTransition_fderiv_cocycle (q₁ q₂ q₃ : M)
    (e₁ e₂ e₃ : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi₁ : ContDiff ℝ ∞ e₁.symm) (he₂ : ContDiff ℝ ∞ e₂)
    (hi₂ : ContDiff ℝ ∞ e₂.symm) (he₃ : ContDiff ℝ ∞ e₃)
    {p : M} (h₁ : p ∈ (surfacePhaseChart q₁ e₁).source)
    (h₂ : p ∈ (surfacePhaseChart q₂ e₂).source)
    (h₃ : p ∈ (surfacePhaseChart q₃ e₃).source) :
    fderiv ℝ (surfacePhaseTransition q₁ e₁ q₃ e₃) (surfacePhaseChart q₁ e₁ p) =
      (fderiv ℝ (surfacePhaseTransition q₂ e₂ q₃ e₃) (surfacePhaseChart q₂ e₂ p)).comp
        (fderiv ℝ (surfacePhaseTransition q₁ e₁ q₂ e₂) (surfacePhaseChart q₁ e₁ p)) := by
  have h₁₂ := surfacePhaseTransition_source q₁ q₂ e₁ e₂ h₁ h₂
  have h₂₃ := surfacePhaseTransition_source q₂ q₃ e₂ e₃ h₂ h₃
  have hd₁₂ := (((surfacePhaseTransition_smooth q₁ e₁ hi₁ q₂ e₂ he₂)
    (surfacePhaseChart q₁ e₁ p) h₁₂).contDiffAt
      ((surfacePhaseTransition q₁ e₁ q₂ e₂).open_source.mem_nhds h₁₂)).differentiableAt (by simp)
  have hd₂₃ := (((surfacePhaseTransition_smooth q₂ e₂ hi₂ q₃ e₃ he₃)
    (surfacePhaseChart q₂ e₂ p) h₂₃).contDiffAt
      ((surfacePhaseTransition q₂ e₂ q₃ e₃).open_source.mem_nhds h₂₃)).differentiableAt (by simp)
  have hg := surfacePhaseTransition_cocycle_germ q₁ q₂ q₃ e₁ e₂ e₃ h₁ h₂ h₃
  rw [← hg.fderiv_eq]
  have ht := surfacePhaseTransition_apply q₁ q₂ e₁ e₂ h₁
  rw [fderiv_comp _ (by rwa [ht]) hd₁₂,ht]

end ClosedSurfaceR4

end

end OAI
