import Mathlib
import OAI.Geometry.PrescribedPotential.HessianCommutator
import OAI.Geometry.PrescribedPotential.SobolevDeterminant

namespace OAI

/-! Nonlinear Hessian Commutator. -/

section

 

noncomputable section
open Set Filter Topology Matrix LineDeriv
open scoped ContDiff SchwartzMap Classical Matrix.Norms.Elementwise
namespace NonlinearHessian
open GlobalElliptic Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ}
local instance matrixContinuousSMul (n : ℕ) : ContinuousSMul ℝ (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (ContinuousSMul ℝ (Fin n → Fin n → ℂ))

lemma determinant_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (fun M : Matrix (Fin n) (Fin n) ℂ => M.det) := by
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro j _
  fun_prop

def detDifferential {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ := fderiv ℝ Matrix.det M

lemma detDifferential_hasFDeriv {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    HasFDerivAt Matrix.det (detDifferential M) M :=
  (determinant_contDiff n).differentiable (by simp) M |>.hasFDerivAt

def hessianMatrix (f : 𝓢(EC d, ℂ)) (x : EC d) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => hessianEntrySchwartz i j f x

lemma hessianMatrix_contDiff (f : 𝓢(EC d, ℂ)) : ContDiff ℝ ∞ (hessianMatrix f) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact (hessianEntrySchwartz i j f).smooth'

lemma hessianMatrix_fderiv (f : 𝓢(EC d, ℂ)) (x v : EC d) (i j : Fin d) :
    fderiv ℝ (hessianMatrix f) x v i j = (∂_{v} (hessianEntrySchwartz i j f)) x := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (fun y : EC d => fun (i j : Fin d) => hessianEntrySchwartz i j f y) x v i j = _
  have H : HasFDerivAt (fun y : EC d => fun (i j : Fin d) => hessianEntrySchwartz i j f y)
      (ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
        fderiv ℝ (hessianEntrySchwartz i j f) x) x := by
    apply hasFDerivAt_pi.mpr
    intro i
    apply hasFDerivAt_pi.mpr
    intro j
    exact (hessianEntrySchwartz i j f).smooth'.differentiable (by simp) x |>.hasFDerivAt
  exact congrArg (fun L : EC d →L[ℝ] (Fin d → Fin d → ℂ) => L v i j) H.fderiv

def complexCutoff (κ : 𝓢(EC d, ℝ)) : 𝓢(EC d, ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM κ

@[simp] lemma complexCutoff_apply (κ : 𝓢(EC d, ℝ)) (x : EC d) :
    complexCutoff κ x = (κ x : ℂ) := rfl

def cutoffHessianError (κ : 𝓢(EC d, ℝ)) (v : EC d) (f : 𝓢(EC d, ℂ)) (x : EC d) :
    Matrix (Fin d) (Fin d) ℂ := fun i j => hessianLocalizedError (complexCutoff κ) v i j f x

lemma hessianMatrix_cutoff (κ : 𝓢(EC d, ℝ)) (v : EC d) (f : 𝓢(EC d, ℂ)) (x : EC d) :
    hessianMatrix (SchwartzMap.smulLeftCLM ℂ (complexCutoff κ) (∂_{v} f)) x =
      κ x • fderiv ℝ (hessianMatrix f) x v + cutoffHessianError κ v f x := by
  ext i j
  change hessianEntrySchwartz i j (SchwartzMap.smulLeftCLM ℂ (complexCutoff κ) (∂_{v} f)) x = _
  rw [hessianLocalizedError_identity]
  simp only [_root_.add_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply (complexCutoff κ).hasTemperateGrowth]
  change (κ x : ℂ) • (∂_{v} (hessianEntrySchwartz i j f)) x +
    hessianLocalizedError (complexCutoff κ) v i j f x =
      κ x • (fderiv ℝ (hessianMatrix f) x v i j) + cutoffHessianError κ v f x i j
  rw [hessianMatrix_fderiv]
  simp only [Complex.real_smul]
  rfl

 

lemma determinant_cutoff_commutator
    (κ : 𝓢(EC d, ℝ)) (v : EC d) (f : 𝓢(EC d, ℂ))
    (B : EC d → ℂ) (G : EC d → Matrix (Fin d) (Fin d) ℂ) (x : EC d)
    (hB : DifferentiableAt ℝ B x) (hG : DifferentiableAt ℝ G x) :
    B x * detDifferential (G x + hessianMatrix f x)
        (hessianMatrix (SchwartzMap.smulLeftCLM ℂ (complexCutoff κ) (∂_{v} f)) x) =
      (κ x : ℂ) * fderiv ℝ (fun y => B y * (G y + hessianMatrix f y).det) x v +
      B x * detDifferential (G x + hessianMatrix f x)
        (cutoffHessianError κ v f x - κ x • fderiv ℝ G x v) -
      (κ x : ℂ) * fderiv ℝ B x v * (G x + hessianMatrix f x).det := by
  have hH := (hessianMatrix_contDiff f).differentiable (by simp) x
  have hd := (detDifferential_hasFDeriv (G x + hessianMatrix f x)).comp x
    (hG.hasFDerivAt.add hH.hasFDerivAt)
  have hq := (hB.hasFDerivAt.mul hd).fderiv
  change fderiv ℝ (fun y => B y * (G y + hessianMatrix f y).det) x = _ at hq
  have hqx : fderiv ℝ (fun y => B y * (G y + hessianMatrix f y).det) x v =
      B x * detDifferential (G x + hessianMatrix f x)
        (fderiv ℝ G x v + fderiv ℝ (hessianMatrix f) x v) +
      (G x + hessianMatrix f x).det * fderiv ℝ B x v := by
    rw [hq]
    rfl
  rw [hqx,hessianMatrix_cutoff]
  simp only [map_add,map_sub,map_smul,Complex.real_smul]
  ring
end NonlinearHessian

end
end

end OAI
