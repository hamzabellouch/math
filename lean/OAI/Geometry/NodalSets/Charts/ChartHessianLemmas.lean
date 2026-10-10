import OAI.Geometry.NodalSets.Charts.ChartMetric

namespace OAI

noncomputable section

namespace Yau.Geometry

section

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma quadraticChart_fderiv_apply_hasFDerivAt (y : E) (e : E ≃L[ℝ] E)
    (B : E →L[ℝ] E →L[ℝ] E) (hB : ∀ u v, B u v = B v u) (x u : E) :
    HasFDerivAt (fun z ↦ fderiv ℝ (quadraticChartMap y e B) z u) (-(B.flip u)) x := by
  have h := (ContinuousLinearMap.apply ℝ E u).hasFDerivAt.comp x
    (quadraticChartMap_second y e B hB x)
  convert h using 1 <;> rfl

lemma scalar_chart_first (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (y : E) (e : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) :
    fderiv ℝ (f ∘ quadraticChartMap y e B) 0 = (fderiv ℝ f y).comp e.toContinuousLinearMap := by
  have h := ((hf.differentiable (by simp)).differentiableAt (x := y)).hasFDerivAt
  have h' : HasFDerivAt f (fderiv ℝ f y) (quadraticChartMap y e B 0) := by
    simpa [quadraticChartMap_zero] using h
  exact (h'.comp 0 (quadraticChartMap_deriv_zero y e B)).fderiv

theorem scalar_chart_hessian (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (y : E) (e : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ u v, B u v = B v u) (u v : E) :
    fderiv ℝ (fun x ↦ fderiv ℝ (f ∘ quadraticChartMap y e B) x u) 0 v =
      fderiv ℝ (fderiv ℝ f) y (e v) (e u) - fderiv ℝ f y (B v u) := by
  let F := quadraticChartMap y e B
  have hFs := quadraticChartMap_smooth y e B
  have heq : (fun x ↦ fderiv ℝ (f ∘ F) x u) =
      fun x ↦ fderiv ℝ f (F x) (fderiv ℝ F x u) := by
    funext x
    rw [fderiv_comp x ((hf.differentiable (by simp)) (F x))
      ((hFs.differentiable (by simp)) x)]
    rfl
  rw [heq]
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) y) (F 0) := by
    simpa [F, quadraticChartMap_zero] using
      ((hdf.differentiable (by simp)) y).hasFDerivAt
  have h := (hd.comp 0 (quadraticChartMap_deriv_zero y e B)).clm_apply
    (quadraticChart_fderiv_apply_hasFDerivAt y e B hB 0 u)
  convert congrArg (fun L : E →L[ℝ] ℝ ↦ L v) h.fderiv using 1 <;>
    simp [F, quadraticChartMap_zero, (quadraticChartMap_deriv_zero y e B).fderiv]
  ring

theorem equal_gradient_chart_hessian_difference (f S : E → ℝ)
    (hf : ContDiff ℝ ∞ f) (hS : ContDiff ℝ ∞ S)
    (y : E) (e : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ u v, B u v = B v u) (hfirst : fderiv ℝ f y = fderiv ℝ S y) (u v : E) :
    fderiv ℝ (fun x ↦ fderiv ℝ (f ∘ quadraticChartMap y e B) x u) 0 v -
      fderiv ℝ (fun x ↦ fderiv ℝ (S ∘ quadraticChartMap y e B) x u) 0 v =
      fderiv ℝ (fderiv ℝ f) y (e v) (e u) - fderiv ℝ (fderiv ℝ S) y (e v) (e u) := by
  rw [scalar_chart_hessian f hf y e B hB, scalar_chart_hessian S hS y e B hB, hfirst]
  ring

end

attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def christoffelCovector (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (1/2:ℝ) • (D + D.flip -
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap.comp D.flip)

lemma christoffelCovector_apply (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (u v w : E) :
    christoffelCovector D u v w = (D u v w + D v u w - D w u v)/2 := by
  simp [christoffelCovector, ContinuousLinearMap.flip_apply]
  ring

def christoffelTensor (m : E ≃L[ℝ] E →L[ℝ] ℝ)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E m.symm.toContinuousLinearMap).comp
    (christoffelCovector D)

lemma christoffelTensor_pair (m : E ≃L[ℝ] E →L[ℝ] ℝ)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (u v w : E) :
    m (christoffelTensor m D u v) w = (D u v w + D v u w - D w u v)/2 := by
  change m (m.symm (christoffelCovector D u v)) w = _
  rw [m.apply_symm_apply, christoffelCovector_apply]

lemma christoffelTensor_symmetric (m : E ≃L[ℝ] E →L[ℝ] ℝ)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (hD : ∀ w u v, D w u v = D w v u)
    (u v : E) : christoffelTensor m D u v = christoffelTensor m D v u := by
  apply m.injective
  ext w
  rw [christoffelTensor_pair, christoffelTensor_pair, hD w u v]
  ring

lemma christoffelTensor_cancel (m : E ≃L[ℝ] E →L[ℝ] ℝ)
    (hm : ∀ u v, m u v = m v u)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (hD : ∀ w u v, D w u v = D w v u)
    (w u v : E) :
    D w u v = m (christoffelTensor m D w u) v + m u (christoffelTensor m D w v) := by
  rw [hm u (christoffelTensor m D w v), christoffelTensor_pair, christoffelTensor_pair]
  rw [hD w v u, hD u w v, hD v w u]
  ring

end Yau.Geometry

end

end OAI
