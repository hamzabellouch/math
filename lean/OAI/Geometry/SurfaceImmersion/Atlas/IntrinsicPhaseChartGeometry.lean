import OAI.Geometry.SurfaceImmersion.Geometry.MetricConnectionNaturality
import OAI.Geometry.SurfaceImmersion.Geometry.PreferredJetGeometry

namespace OAI

/-! Transport immersion, preferred normal, convexity and forbidden antipodes
through the genuine inverse phase chart. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes VelocityFrame NormalFrame

lemma inverse_phase_chart_geometry {F n : Base → Fin 4 → ℝ} {φ : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hphase : ∀ x, (e x).1 = φ x)
    (hI : ∀ x ∈ e.source, Function.Injective (fderiv ℝ F x))
    (hN : ∀ x ∈ e.source, (∀ v, fderiv ℝ F x v ⬝ᵥ n x = 0) ∧ n x ⬝ᵥ n x = 1)
    (hH : ∀ x ∈ e.source, ∀ v : Base, v ≠ 0 →
      0 < coordinateMetricHessian (inducedCoordinateMetric F) φ x v v) :
    ∀ p ∈ e.target,
      Function.Injective (fderiv ℝ (F ∘ e.symm) p) ∧
      (coordDeriv dx (F ∘ e.symm) p ⬝ᵥ (n ∘ e.symm) p = 0 ∧
       coordDeriv dy (F ∘ e.symm) p ⬝ᵥ (n ∘ e.symm) p = 0 ∧
       (n ∘ e.symm) p ⬝ᵥ (n ∘ e.symm) p = 1) ∧
      0 < coordinateMetricHessian (inducedCoordinateMetric (F ∘ e.symm)) Prod.fst p dy dy := by
  intro p hp
  have hip := inverse_chart_derivative_injective e he hi hp
  have hD : coordDet (fderiv ℝ e.symm p) ≠ 0 :=
    coordDet_fderiv_ne_zero_of_local_inverse e.open_target e.open_source hi.contDiffOn
      he.contDiffOn (fun _ hx => e.map_target hx) (fun x hx => e.right_inv hx) hp
  have hv : fderiv ℝ e.symm p dy ≠ 0 := by
    intro hz
    have heq := hip (hz.trans (map_zero (fderiv ℝ e.symm p)).symm)
    exact (show (dy : Base) ≠ 0 from by simp [dy]) heq
  refine ⟨?_,?_,?_⟩
  · rw [fderiv_comp p (hF.differentiable (by simp) _) (hi.differentiable (by simp) _)]
    exact (hI _ (e.map_target hp)).comp hip
  · have hc (v : Base) :
        coordDeriv v (F ∘ e.symm) p ⬝ᵥ (n ∘ e.symm) p = 0 := by
      rw [coordDeriv_comp_smooth hF hi]
      exact (hN _ (e.map_target hp)).1 _
    exact ⟨hc dx,hc dy,(hN _ (e.map_target hp)).2⟩
  · have hcomp : φ ∘ e.symm =ᶠ[𝓝 p] Prod.fst := by
      filter_upwards [e.open_target.mem_nhds hp] with x hx
      change φ (e.symm x) = x.1
      rw [← hphase,e.right_inv hx]
    rw [phase_chart_hessian_dy hF hφ hi p hcomp (hI _ (e.map_target hp)) hD]
    exact hH _ (e.map_target hp) _ hv

lemma inverse_phase_chart_antipode {F n : Base → Fin 4 → ℝ}
    (hF : ContDiff ℝ ∞ F)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {p : Base} (hp : p ∈ e.target)
    (hI : Function.Injective (fderiv ℝ F (e.symm p)))
    (hB : ∀ v : Base, v ≠ 0 → realSecondForm F v v (e.symm p) ≠ 0 ∧
      normalize (realSecondForm F v v (e.symm p)) ≠ -n (e.symm p)) :
    realSecondForm (F ∘ e.symm) dy dy p ≠ 0 ∧
      normalize (realSecondForm (F ∘ e.symm) dy dy p) ≠ -(n ∘ e.symm) p := by
  have hD : coordDet (fderiv ℝ e.symm p) ≠ 0 :=
    coordDet_fderiv_ne_zero_of_local_inverse e.open_target e.open_source hi.contDiffOn
      he.contDiffOn (fun _ hx => e.map_target hx) (fun x hx => e.right_inv hx) hp
  have hv : fderiv ℝ e.symm p dy ≠ 0 := by
    intro hz
    have heq := inverse_chart_derivative_injective e he hi hp
      (hz.trans (map_zero (fderiv ℝ e.symm p)).symm)
    exact (show (dy : Base) ≠ 0 from by simp [dy]) heq
  rw [realSecondForm_comp_smooth hF hi dy dy p (gramDet_ne_zero_of_injective _ hI) hD]
  exact hB _ hv

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
