import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianResponse
import OAI.Probability.SKBarriers.Hierarchy.HierarchyDensity
import OAI.Probability.SKBarriers.Scalar.ScalarCurvature

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def rootGradient (n : ℕ) (f : ParameterSpace n → ℝ) (z : ParameterSpace n) : ℝ :=
  fderiv ℝ f z (parameterAxis n)

def rootHessian (n : ℕ) (f : ParameterSpace n → ℝ) (z : ParameterSpace n) : ℝ :=
  fderiv ℝ (fderiv ℝ f) z (parameterAxis n) (parameterAxis n)

def RootSpinCurvature (n : ℕ) (f : ParameterSpace n → ℝ) : Prop :=
  ∀ z, 0 < rootHessian n f z ∧ rootHessian n f z ≤ 1-(rootGradient n f z)^2

theorem RootSpinCurvature.bounds {n : ℕ} {f : ParameterSpace n → ℝ}
    (h : RootSpinCurvature n f) (z : ParameterSpace n) :
    |rootGradient n f z| ≤ 1 ∧ |rootHessian n f z| ≤ 1 := by
  have H := h z
  refine ⟨(sq_le_one_iff_abs_le_one _).mp (by linarith),?_⟩
  rw [abs_of_pos H.1]
  linarith [sq_nonneg (rootGradient n f z)]

theorem RootSpinCurvature.gaussianStep {n : ℕ} {f : ParameterSpace (n+1) → ℝ}
    (h : RootSpinCurvature (n+1) f) (hf : BoundedDerivs f) {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) :
    RootSpinCurvature n (gaussianStep m f) := by
  intro z
  exact gaussianStep_spin_curvature hf hm (parameterAxis n) z (fun y => h (z,y))

theorem rootGradient_continuous (n : ℕ) {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) :
    Continuous (rootGradient n f) :=
  (hf.1.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem rootHessian_continuous (n : ℕ) {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) :
    Continuous (rootHessian n f) :=
  ((hf.1.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
    continuous_const |>.clm_apply continuous_const

theorem rootLine_hasDerivAt (n : ℕ) {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (z : ParameterSpace n) (t : ℝ) :
    HasDerivAt (fun a : ℝ => f (z+a • parameterAxis n))
      (rootGradient n f (z+t • parameterAxis n)) t := by
  have hd : HasDerivAt (fun a : ℝ => z+a • parameterAxis n) (parameterAxis n) t := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const (parameterAxis n)).const_add z
  exact ((hf.1.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t hd)

theorem rootGradientLine_hasDerivAt (n : ℕ) {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (z : ParameterSpace n) (t : ℝ) :
    HasDerivAt (fun a : ℝ => rootGradient n f (z+a • parameterAxis n))
      (rootHessian n f (z+t • parameterAxis n)) t := by
  have hd : HasDerivAt (fun a : ℝ => z+a • parameterAxis n) (parameterAxis n) t := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const (parameterAxis n)).const_add z
  have h := ((directionalGradient_contDiff f hf.1 (parameterAxis n)).differentiable
      (by norm_num) (z+t • parameterAxis n)).hasFDerivAt.comp_hasDerivAt t hd
  rw [fderiv_directionalGradient f hf.1] at h
  exact h

theorem rootShift_value_bound (n : ℕ) {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (h : RootSpinCurvature n f) (z : ParameterSpace n) (t : ℝ) :
    |f (z+t • parameterAxis n)-f z| ≤ |t| := by
  have hd := rootLine_hasDerivAt n hf z
  have hLip : LipschitzWith 1 (fun a : ℝ => f (z+a • parameterAxis n)) :=
    lipschitzWith_of_nnnorm_deriv_le (fun a => (hd a).differentiableAt) (fun a => by
      rw [(hd a).deriv]
      exact_mod_cast (h.bounds (z+a • parameterAxis n)).1)
  simpa only [Real.norm_eq_abs,NNReal.coe_one,one_mul,zero_smul,add_zero,sub_zero] using hLip.norm_sub_le t 0

theorem rootShift_gradient_bound (n : ℕ) {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (h : RootSpinCurvature n f) (z : ParameterSpace n) (t : ℝ) :
    |rootGradient n f (z+t • parameterAxis n)-rootGradient n f z| ≤ |t| := by
  have hd := rootGradientLine_hasDerivAt n hf z
  have hLip : LipschitzWith 1 (fun a : ℝ => rootGradient n f (z+a • parameterAxis n)) :=
    lipschitzWith_of_nnnorm_deriv_le (fun a => (hd a).differentiableAt) (fun a => by
      rw [(hd a).deriv]
      exact_mod_cast (h.bounds (z+a • parameterAxis n)).2)
  simpa only [Real.norm_eq_abs,NNReal.coe_one,one_mul,zero_smul,add_zero,sub_zero] using hLip.norm_sub_le t 0

theorem rootGradient_fst (n : ℕ) {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (z : ParameterSpace (n+1)) :
    rootGradient (n+1) (fun z : ParameterSpace (n+1) => f z.1) z = rootGradient n f z.1 := by
  let P : ParameterSpace (n+1) →L[ℝ] ParameterSpace n := ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ
  have hd := (hf.1.differentiable (by norm_num) z.1).hasFDerivAt.comp z P.hasFDerivAt
  unfold rootGradient
  have he : fderiv ℝ (fun z : ParameterSpace (n+1) => f z.1) z =
      (fderiv ℝ f z.1).comp P := hd.fderiv
  rw [he]
  rfl

theorem rootGradient_penalty_succ (n : ℕ) (m : Fin (n+1) → ℝ) (u : ℝ)
    {f : ParameterSpace (n+1) → ℝ} (hf : BoundedDerivs f) (z : ParameterSpace (n+1)) :
    rootGradient (n+1) (hierarchyPenalty (n+1) m u f) z =
      (u-m (Fin.last n))*rootGradient (n+1) f z+
      rootGradient n (hierarchyPenalty n (fun i => m i.castSucc) (m (Fin.last n))
        (gaussianStep (m (Fin.last n)) f)) z.1 := by
  let g := hierarchyPenalty n (fun i => m i.castSucc) (m (Fin.last n)) (gaussianStep (m (Fin.last n)) f)
  have hg : BoundedDerivs g := hierarchyPenalty_boundedDerivs _ _ _ _ (hf.gaussianStep _)
  have hgP := hg.compCLM (ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ)
  have hd := ((hf.1.differentiable (by norm_num) z).hasFDerivAt.const_mul (u-m (Fin.last n))).add
    (hgP.1.differentiable (by norm_num) z).hasFDerivAt
  change fderiv ℝ (fun z : ParameterSpace (n+1) => (u-m (Fin.last n))*f z+g z.1) z _ = _
  have he : fderiv ℝ (fun z : ParameterSpace (n+1) => (u-m (Fin.last n))*f z+g z.1) z =
      ((u-m (Fin.last n)) • fderiv ℝ f z)+fderiv ℝ (fun z : ParameterSpace (n+1) => g z.1) z := hd.fderiv
  rw [he]
  simp only [add_apply,smul_apply,smul_eq_mul]
  change (u-m (Fin.last n))*rootGradient (n+1) f z+
    rootGradient (n+1) (fun z : ParameterSpace (n+1) => g z.1) z = _
  rw [rootGradient_fst n hg]

end SK.Analytic

end
end

end OAI
