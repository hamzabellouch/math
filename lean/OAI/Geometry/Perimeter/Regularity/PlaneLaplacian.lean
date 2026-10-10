import OAI.Geometry.Perimeter.Regularity.NormalWindowTest

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace ContDiff
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n m : ℕ} {v : Euc n}

def chartProjection (e : Euc m ≃ₗᵢ[ℝ] normalPlane v) : Euc n →L[ℝ] Euc m :=
  e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (normalProjection v)

def chartInclusion (e : Euc m ≃ₗᵢ[ℝ] normalPlane v) : Euc m →L[ℝ] Euc n :=
  (normalPlane v).subtypeL.comp e.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem chartProjection_inclusion (e : Euc m ≃ₗᵢ[ℝ] normalPlane v) (y : Euc m) :
    chartProjection e (chartInclusion e y)=y := by
  change e.symm (normalProjection v (e y))=y
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,e.symm_apply_apply]

@[simp] theorem chartProjection_normal (e : Euc m ≃ₗᵢ[ℝ] normalPlane v) :
    chartProjection e v=0 := by
  have h : normalProjection v v = 0 :=
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
      ((ℝ ∙ v).le_orthogonal_orthogonal (Submodule.mem_span_singleton_self v))
  change e.symm (normalProjection v v)=0
  rw [h,map_zero]

theorem chartInclusion_inner (e : Euc m ≃ₗᵢ[ℝ] normalPlane v) (y : Euc m) (x : Euc n) :
    inner ℝ (chartInclusion e y) x = inner ℝ y (chartProjection e x) := by
  change inner ℝ (e y:Euc n) x = inner ℝ y (e.symm (normalProjection v x))
  rw [← (normalPlane v).inner_orthogonalProjectionOnto_eq_of_mem_left (e y) x]
  simpa only [e.apply_symm_apply] using (e.inner_map_map y (e.symm (normalProjection v x)))

theorem gradient_chart_lift {ψ : Euc m → ℝ} (hψ : Differentiable ℝ ψ)
    (e : Euc m ≃ₗᵢ[ℝ] normalPlane v) (x : Euc n) :
    gradient (fun z ↦ ψ (chartProjection e z)) x =
      chartInclusion e (gradient ψ (chartProjection e x)) := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left,chartInclusion_inner,inner_gradient_left]
  change fderiv ℝ (ψ ∘ chartProjection e) x z = _
  rw [fderiv_comp x (hψ _) (chartProjection e).differentiableAt,(chartProjection e).fderiv]
  rfl

theorem divergence_eq_trace {V : Euc n → Euc n} (x : Euc n) :
    divergence V x = (fderiv ℝ V x).toLinearMap.trace ℝ (Euc n) := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin n) ℝ)]
  rfl

theorem planar_laplacian_chart_lift {ψ : Euc m → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (e : Euc m ≃ₗᵢ[ℝ] normalPlane v) (x : Euc n) :
    planarDivergence v (gradient (fun z ↦ ψ (chartProjection e z))) x =
      divergence (gradient ψ) (chartProjection e x) := by
  have hg := gradient_contDiff hψ
  have he : gradient (fun z ↦ ψ (chartProjection e z)) =
      fun z ↦ chartInclusion e (gradient ψ (chartProjection e z)) :=
    funext (gradient_chart_lift (hψ.differentiable (by simp)) e)
  have hd : fderiv ℝ (gradient (fun z ↦ ψ (chartProjection e z))) x =
      (chartInclusion e).comp ((fderiv ℝ (gradient ψ) (chartProjection e x)).comp (chartProjection e)) := by
    rw [he]
    exact (((chartInclusion e).hasFDerivAt.comp x
      (((hg.differentiable (by simp) _).hasFDerivAt).comp x
        (chartProjection e).hasFDerivAt))).fderiv
  rw [planarDivergence,divergence_eq_trace,hd,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,chartProjection_normal,map_zero,map_zero,inner_zero_right,sub_zero,
    divergence_eq_trace]
  change LinearMap.trace ℝ (Euc n)
    ((chartInclusion e).toLinearMap.comp
      ((fderiv ℝ (gradient ψ) (chartProjection e x)).toLinearMap.comp
        (chartProjection e).toLinearMap)) = _
  rw [LinearMap.trace_comp_comm']
  have hi : (chartProjection e).toLinearMap.comp (chartInclusion e).toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro y
    exact chartProjection_inclusion e y
  rw [LinearMap.comp_assoc,hi,LinearMap.comp_id]

end RPISingularHarnack

end

end OAI
