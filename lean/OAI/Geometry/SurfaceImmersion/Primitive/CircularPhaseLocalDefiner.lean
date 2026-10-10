import OAI.Geometry.SurfaceImmersion.Atlas.PhaseTransverseDefiner
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteBoundaryLocalDefiners

namespace OAI

/-! Actual coordinate-circle defining functions in a nonlinear phase chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma circular_boundary_phase_definer (q b : M) (ell : Base) (L r : ℝ)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hdom : e.source ⊆ (coordinateChart q).target)
    (hphase : ∀ x, (e x).1 = centeredConvexPhase ell L (coordinateChart q q) x)
    {p : Base} (hp : p ∈ e.target)
    (hboundary : (coordinateChart q).symm (e.symm p) ∈ circularBoundary b r)
    (htrans : circularPhaseDerivative q b ell L ((coordinateChart q).symm (e.symm p)) ≠ 0) :
    ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧ ∃ g : Base → ℝ,
      ContDiffOn ℝ ∞ g N ∧
      (∀ x ∈ N, (coordinateChart q).symm (e.symm x) ∈ circularBoundary b r → g x = 0) ∧
      fderiv ℝ g p dy ≠ 0 := by
  let m : Base → M := fun x => (coordinateChart q).symm (e.symm x)
  let f : Base → Base := coordinateTransition b q ∘ e.symm
  let φ : Base → ℝ := centeredAtlasPhase q ell L ∘ (coordinateChart b).symm
  let ρ : Base → ℝ := circularRadiusSquared (coordinateChart b b)
  let N : Set Base := e.target ∩ e.symm ⁻¹' (coordinateTransition b q).source
  have hN : IsOpen N := e.open_target.inter
    ((coordinateTransition b q).open_source.preimage hi.continuous)
  have hxp : e.symm p ∈ (coordinateTransition b q).source :=
    ⟨hdom (e.map_target hp),hboundary.1⟩
  have hpN : p ∈ N := ⟨hp,hxp⟩
  have hf : ContDiffOn ℝ ∞ f N :=
    (coordinateTransition_smoothOn b q).comp hi.contDiffOn (fun _ hx => hx.2)
  have hfp : DifferentiableAt ℝ f p := (hf.contDiffAt (hN.mem_nhds hpN)).differentiableAt (by simp)
  have hqm : m p ∈ (coordinateChart q).source := (coordinateChart q).map_target hxp.1
  have hfpeq : f p = coordinateChart b (m p) := rfl
  have hback : f p ∈ (coordinateTransition q b).source := by
    rw [hfpeq]
    exact coordinateTransition_mem_chart q b hboundary.1 hqm
  have hφ : DifferentiableAt ℝ φ (f p) :=
    ((centeredConvexPhase_smooth ell L (coordinateChart q q)).differentiable (by simp) _).comp _
      (((coordinateTransition_smoothOn q b).contDiffAt
        ((coordinateTransition q b).open_source.mem_nhds hback)).differentiableAt (by simp))
  have hcomp : φ ∘ f =ᶠ[𝓝 p] Prod.fst := by
    filter_upwards [hN.mem_nhds hpN] with x hx
    have hbx : m x ∈ (coordinateChart b).source := hx.2.2
    change centeredConvexPhase ell L (coordinateChart q q)
      (coordinateChart q ((coordinateChart b).symm (coordinateChart b (m x)))) = x.1
    rw [(coordinateChart b).left_inv hbx]
    change centeredConvexPhase ell L (coordinateChart q q)
      (coordinateChart q ((coordinateChart q).symm (e.symm x))) = x.1
    rw [(coordinateChart q).right_inv hx.2.1,← hphase,e.right_inv hx.1]
  have hdet : coordDet (fderiv ℝ f p) ≠ 0 := by
    rw [show f = coordinateTransition b q ∘ e.symm from rfl,
      fderiv_comp p (((coordinateTransition_smoothOn b q).contDiffAt
        ((coordinateTransition b q).open_source.mem_nhds hxp)).differentiableAt (by simp))
        (hi.differentiable (by simp) p),coordDet_comp]
    exact mul_ne_zero (coordinateTransition_det_ne b q hxp)
      (coordDet_fderiv_ne_zero_of_local_inverse e.open_target e.open_source hi.contDiffOn
        he.contDiffOn (fun _ hx => e.map_target hx) (fun x hx => e.right_inv hx) hp)
  have hangle : phaseLinear (phaseDerivative φ (f p))
      (circularAngularTangent (coordinateChart b b) (f p)) ≠ 0 := htrans
  have hcross : covectorDet (phaseDerivative φ (f p)) (phaseDerivative ρ (f p)) ≠ 0 := by
    rw [show ρ = circularRadiusSquared (coordinateChart b b) from rfl,
      circular_radius_phase_determinant]
    exact mul_ne_zero (by norm_num) hangle
  have hd := phase_chart_transverse_definer_at hφ
    ((circularRadiusSquared_smooth (coordinateChart b b)).differentiable (by simp) _) hfp
    hcomp hdet hcross
  refine ⟨N,hN,hpN,fun x => ρ (f x)-r^2,
    ((circularRadiusSquared_smooth (coordinateChart b b)).comp_contDiffOn hf).sub contDiffOn_const,
    ?_,?_⟩
  · intro x hx hb
    exact sub_eq_zero.mpr hb.2
  · change fderiv ℝ ((circularRadiusSquared (coordinateChart b b) ∘ f) - (fun _ => r^2)) p dy ≠ 0
    rw [fderiv_sub (((circularRadiusSquared_smooth (coordinateChart b b)).comp_contDiffOn hf).contDiffAt
      (hN.mem_nhds hpN) |>.differentiableAt (by simp)) (differentiableAt_const _)]
    simpa using hd

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
