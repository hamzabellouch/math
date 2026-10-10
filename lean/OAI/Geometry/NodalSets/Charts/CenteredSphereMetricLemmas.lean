import OAI.Geometry.NodalSets.Charts.CenteredSphereSecondJet

namespace OAI

noncomputable section

namespace Yau.Target

open Manifold Matrix
open scoped ContDiff RealInnerProductSpace

lemma sphereRoundChartMatrix_inner (p : Base) (y : BaseModel) (i j : Fin 4) :
    sphereRoundChartMatrix p y i j =
      ⟪sphereChartDerivative p y (EuclideanSpace.basisFun (Fin 4) ℝ i),
        sphereChartDerivative p y (EuclideanSpace.basisFun (Fin 4) ℝ j)⟫ := by
  simp [sphereRoundChartMatrix,Matrix.mul_apply,Matrix.transpose_apply,
    sphereChartFrame_apply,PiLp.inner_apply,mul_comm]

lemma centeredSphereRoundMatrix (p : Base) : sphereRoundChartMatrix p 0 = 1 := by
  ext i j
  rw [sphereRoundChartMatrix_inner,centeredSphereChart_derivative]
  change ⟪centeredSphereIsometry p _,centeredSphereIsometry p _⟫ = _
  rw [(centeredSphereIsometry p).inner_map_map]
  simp [PiLp.inner_apply,EuclideanSpace.basisFun_apply,Matrix.one_apply]

lemma centeredSphereRoundMatrix_entry_hasFDerivAt (p : Base) (i j : Fin 4) :
    HasFDerivAt (fun y ↦ sphereRoundChartMatrix p y i j) (0 : BaseModel →L[ℝ] ℝ) 0 := by
  simp_rw [sphereRoundChartMatrix_inner]
  have h := (centeredSphereChart_direction_hasFDerivAt p
    (EuclideanSpace.basisFun (Fin 4) ℝ i)).inner ℝ
      (centeredSphereChart_direction_hasFDerivAt p (EuclideanSpace.basisFun (Fin 4) ℝ j))
  convert! h using 1
  ext w
  simp [centeredSphereChart_derivative,inner_smul_left,inner_smul_right,
    centeredSphereIsometry_orthogonal,real_inner_comm]

lemma centeredSphereRoundMatrix_hasFDerivAt (p : Base) :
    HasFDerivAt (sphereRoundChartMatrix p)
      (0 : BaseModel →L[ℝ] Matrix (Fin 4) (Fin 4) ℝ) 0 := by
  have h := hasFDerivAt_pi.mpr (fun i ↦ hasFDerivAt_pi.mpr
    (fun j ↦ centeredSphereRoundMatrix_entry_hasFDerivAt p i j))
  convert! h using 1

open Manifold Filter
open scoped Topology

lemma sphere_restriction_chart_second_local (f : AmbientBase → ℝ) (p : Base) (hf : ContDiffAt ℝ ∞ f (p : AmbientBase)) (v w : BaseModel) :
    fderiv ℝ (fderiv ℝ ((fun x : Base ↦ f x) ∘ (extChartAt (𝓡 4) p).symm)) 0 v w =
      fderiv ℝ (fderiv ℝ f) (p : AmbientBase)
        (centeredSphereIsometry p v) (centeredSphereIsometry p w) -
      ⟪v,w⟫ * fderiv ℝ f (p : AmbientBase) (p : AmbientBase) := by
  let : ContinuousSMul ℝ BaseModel := IsBoundedSMul.continuousSMul
  let F : BaseModel → AmbientBase := (Subtype.val : Base → AmbientBase) ∘ (extChartAt (𝓡 4) p).symm
  have hFs : ContDiff ℝ ∞ F := by
    rw [show F = stereoInvFunAux (-(p : AmbientBase)) ∘ (centeredSphereIsometry p) from
      centeredSphereChart_inverse p]
    exact contDiff_stereoInvFunAux.comp (centeredSphereIsometry p).contDiff
  have hF0 : F 0 = (p : AmbientBase) := by exact congrArg (Subtype.val : Base → AmbientBase) (centeredSphereChart_inverse_zero p)
  have hFd (y : BaseModel) : fderiv ℝ F y = sphereChartDerivative p y :=
    (sphereChartDerivative_eq_fderiv p (by rw [centeredSphereChart_target]; trivial)).symm
  have hf0 : ContDiffAt ℝ ∞ f (F 0) := hF0.symm ▸ hf
  have hdf := (hf0.fderiv_right (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by simp)).differentiableAt (by simp)
  have hdF : HasFDerivAt F (centeredSphereIsometry p).toContinuousLinearMap 0 := by
    convert! (hFs.differentiable (by simp) 0).hasFDerivAt using 1
    rw [hFd,centeredSphereChart_derivative]
  have hG := hdf.hasFDerivAt.comp 0 hdF
  have h := hG.clm_apply (centeredSphereChart_direction_hasFDerivAt p w)
  have he : (fun y ↦ fderiv ℝ (f ∘ F) y w) =ᶠ[𝓝 0]
      (fun y ↦ fderiv ℝ f (F y) (sphereChartDerivative p y w)) := by
    have hnear := ((hf0.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by simp)).filter_mono
      (hFs.continuous.continuousAt.tendsto)
    filter_upwards [hnear] with y hy
    change ContDiffAt ℝ 1 f (F y) at hy
    rw [fderiv_comp y (hy.differentiableAt (by simp)) (hFs.differentiable (by simp) _),hFd]
    rfl
  have hQ := ((hf0.comp 0 hFs.contDiffAt).fderiv_right (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by simp)).differentiableAt (by simp)
  have hE := congrArg (fun L : BaseModel →L[ℝ] ℝ ↦ L v)
    (hQ.hasFDerivAt.clm_apply (hasFDerivAt_const w (0:BaseModel))).fderiv
  simp only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply] at hE
  change fderiv ℝ (fderiv ℝ (f ∘ F)) 0 v w = _
  change HasFDerivAt (fun y ↦ fderiv ℝ f (F y) (sphereChartDerivative p y w)) _ 0 at h
  rw [← hE,he.fderiv_eq,h.fderiv]
  simp [hF0,centeredSphereChart_derivative,real_inner_comm,sub_eq_add_neg,add_comm]

open Manifold

lemma sphere_restriction_chart_second (f : AmbientBase → ℝ) (hf : ContDiff ℝ ∞ f)
    (p : Base) (v w : BaseModel) :
    fderiv ℝ (fderiv ℝ ((fun x : Base ↦ f x) ∘ (extChartAt (𝓡 4) p).symm)) 0 v w =
      fderiv ℝ (fderiv ℝ f) (p : AmbientBase)
        (centeredSphereIsometry p v) (centeredSphereIsometry p w) -
      ⟪v,w⟫ * fderiv ℝ f (p : AmbientBase) (p : AmbientBase) := by
  let : ContinuousSMul ℝ BaseModel := IsBoundedSMul.continuousSMul
  let F : BaseModel → AmbientBase := (Subtype.val : Base → AmbientBase) ∘ (extChartAt (𝓡 4) p).symm
  have hFs : ContDiff ℝ ∞ F := by
    rw [show F = stereoInvFunAux (-(p : AmbientBase)) ∘ (centeredSphereIsometry p) from
      centeredSphereChart_inverse p]
    exact contDiff_stereoInvFunAux.comp (centeredSphereIsometry p).contDiff
  have hF0 : F 0 = (p : AmbientBase) := by exact congrArg (Subtype.val : Base → AmbientBase) (centeredSphereChart_inverse_zero p)
  have hFd (y : BaseModel) : fderiv ℝ F y = sphereChartDerivative p y :=
    (sphereChartDerivative_eq_fderiv p (by rw [centeredSphereChart_target]; trivial)).symm
  have hdf := (hf.fderiv_right (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by simp)).differentiable (by simp)
  have hdF : HasFDerivAt F (centeredSphereIsometry p).toContinuousLinearMap 0 := by
    convert! (hFs.differentiable (by simp) 0).hasFDerivAt using 1
    rw [hFd,centeredSphereChart_derivative]
  have hG := (hdf (F 0)).hasFDerivAt.comp 0 hdF
  have h := hG.clm_apply (centeredSphereChart_direction_hasFDerivAt p w)
  have he : (fun y ↦ fderiv ℝ (f ∘ F) y w) =
      (fun y ↦ fderiv ℝ f (F y) (sphereChartDerivative p y w)) := by
    funext y
    rw [fderiv_comp y (hf.differentiable (by simp) _) (hFs.differentiable (by simp) _),hFd]
    rfl
  have hQ := ((hf.comp hFs).fderiv_right (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by simp)).differentiable (by simp) 0
  have hE := congrArg (fun L : BaseModel →L[ℝ] ℝ ↦ L v)
    (hQ.hasFDerivAt.clm_apply (hasFDerivAt_const w (0:BaseModel))).fderiv
  simp only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply] at hE
  change fderiv ℝ (fderiv ℝ (f ∘ F)) 0 v w = _
  change HasFDerivAt (fun y ↦ fderiv ℝ f (F y) (sphereChartDerivative p y w)) _ 0 at h
  rw [← hE,he,h.fderiv]
  simp [hF0,centeredSphereChart_derivative,real_inner_comm,sub_eq_add_neg,add_comm]

end Yau.Target

end

end OAI
