import OAI.Geometry.SurfaceImmersion.Atlas.ExtendedPhaseChart
import OAI.Geometry.Immersion.ClosedSurface.JacobianBounds

namespace OAI

/-! Good phase directions remain good in their actual nonlinear phase charts. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma phaseDerivative_comp_smooth {φ : Base → ℝ} {f : Base → Base}
    (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f) (p : Base) :
    phaseDerivative (φ ∘ f) p = pullCovector (fderiv ℝ f p) (phaseDerivative φ (f p)) := by
  unfold phaseDerivative
  rw [fderiv_comp p (hφ.differentiable (by simp) _) (hf.differentiable (by simp) _)]
  change ((fderiv ℝ φ (f p)) ((fderiv ℝ f p) dx),
    (fderiv ℝ φ (f p)) ((fderiv ℝ f p) dy)) = _
  conv_lhs => rw [← phaseLinear_phaseDerivative φ (f p)]
  rfl

lemma inverse_chart_derivative (e : OpenPartialHomeomorph Base Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm) {y : Base} (hy : y ∈ e.target) :
    (fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y) = ContinuousLinearMap.id ℝ Base := by
  have hh : e ∘ e.symm =ᶠ[𝓝 y] id := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact e.right_inv hz
  rw [← fderiv_comp y (he.differentiable (by simp) _) (hi.differentiable (by simp) _),
    hh.fderiv_eq,fderiv_id]

lemma inverse_chart_derivative_injective (e : OpenPartialHomeomorph Base Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm) {y : Base} (hy : y ∈ e.target) :
    Function.Injective (fderiv ℝ e.symm y) := by
  have hh := inverse_chart_derivative e he hi hy
  intro u v huv
  have h := congrArg (fderiv ℝ e (e.symm y)) huv
  change ((fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y)) u =
    ((fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y)) v at h
  simpa only [hh,ContinuousLinearMap.id_apply] using h

lemma inverse_chart_phase_covector {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : OpenPartialHomeomorph Base Base) (hi : ContDiff ℝ ∞ e.symm)
    (hphase : ∀ x, (e x).1 = φ x) {y : Base} (hy : y ∈ e.target) :
    pullCovector (fderiv ℝ e.symm y) (phaseDerivative φ (e.symm y)) = dx := by
  have hh : φ ∘ e.symm =ᶠ[𝓝 y] Prod.fst := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    change φ (e.symm z) = z.1
    rw [← hphase,e.right_inv hz]
  rw [← phaseDerivative_comp_smooth hφ hi]
  unfold phaseDerivative
  rw [hh.fderiv_eq,fderiv_fst]
  rfl

/-- A nonlinear first-coordinate chart carries precisely the good direction
needed by the local free and forced mode constructions. -/
theorem realModeDomain_smooth_phase_chart {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hphase : ∀ x, (e x).1 = φ x)
    (hImm : ∀ x ∈ e.source, Function.Injective (fderiv ℝ F x))
    (hgood : ∀ x ∈ e.source, Good (realSecondTensor F x) (phaseDerivative φ x)) :
    RealModeDomain (F ∘ e.symm) e.target := by
  refine ⟨e.open_target,?_,?_⟩
  · intro y hy
    apply gramDet_ne_zero_of_injective
    rw [fderiv_comp y (hF.differentiable (by simp) _) (hi.differentiable (by simp) _)]
    exact (hImm _ (e.map_target hy)).comp (inverse_chart_derivative_injective e he hi hy)
  · intro y hy
    have hD := gramDet_ne_zero_of_injective (fderiv ℝ F (e.symm y)) (hImm _ (e.map_target hy))
    have hdet : coordDet (fderiv ℝ e.symm y) ≠ 0 :=
      coordDet_fderiv_ne_zero_of_local_inverse e.open_target e.open_source
        hi.contDiffOn he.contDiffOn (fun _ hz => e.map_target hz) (fun z hz => e.right_inv hz) hy
    have hq := phase_length_comp_smooth hF hi (phaseDerivative φ (e.symm y)) y hD hdet
    rw [inverse_chart_phase_covector hφ e hi hphase hy] at hq
    have hn : secondQuadratic (realSecondTensor (F ∘ e.symm) y) dy ≠ 0 := by
      simp only [dx,neg_zero] at hq
      change secondQuadratic (realSecondTensor (F ∘ e.symm) y) (0,1) ≠ 0
      rw [hq]
      exact smul_ne_zero (pow_ne_zero 2 hdet) (hgood _ (e.map_target hy)).2
    change realSecondForm (F ∘ e.symm) dy dy y ≠ 0
    rw [realSecondForm_quadratic (hF.comp hi)]
    exact hn

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
