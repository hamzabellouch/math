import Mathlib
import OAI.Geometry.PrescribedRicci.FiniteCofactor

namespace OAI

/-! Cofactor Bilin. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff SchwartzMap Classical BoundedContinuousFunction Matrix.Norms.Elementwise
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart FrozenPoisson
variable {d : ℕ}
local instance : NormedAddCommGroup (Bilin (EC d)) := inferInstance
local instance : NormedSpace ℝ (Bilin (EC d)) := inferInstance

def cofactorBilinLinear (c : ℂ) (M : Matrix (Fin d) (Fin d) ℂ) : Bilin (EC d) →ₗ[ℝ] ℝ where
  toFun B := (c * NonlinearHessian.detDifferential M (GluingData.cofactorMatrix B)).re
  map_add' B C := by
    simp only [GluingData.cofactorMatrix,pullBilin_add,hermitianPartMatrix_add,map_add,mul_add,Complex.add_re]
  map_smul' r B := by
    simp only [GluingData.cofactorMatrix,pullBilin_smul,hermitianPartMatrix_smul,map_smul,
      RingHom.id_apply,Complex.real_smul,smul_eq_mul]
    simp only [Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
    ring

def cofactorBilin (c : ℂ) (M : Matrix (Fin d) (Fin d) ℂ) : SecondOrder (EC d) :=
  by
    change Bilin (EC d) →L[ℝ] ℝ
    exact (cofactorBilinLinear c M).toContinuousLinearMap

lemma cofactorBilin_apply (c : ℂ) (M : Matrix (Fin d) (Fin d) ℂ) (B : Bilin (EC d)) :
    cofactorBilin c M B = (c * NonlinearHessian.detDifferential M (GluingData.cofactorMatrix B)).re := rfl

lemma cofactorBilin_expansion (c : ℂ) (M : Matrix (Fin d) (Fin d) ℂ) (B : Bilin (EC d)) :
    (cofactorBilin c M B : ℂ) = ∑ i, ∑ j,
      (cofactorBilin c M (rankTwo (stdOrthonormalBasis ℝ (EC d) i)
        (stdOrthonormalBasis ℝ (EC d) j)) : ℂ) *
        (B (stdOrthonormalBasis ℝ (EC d) i) (stdOrthonormalBasis ℝ (EC d) j) : ℂ) := by
  conv_lhs => rw [bilin_expansion (stdOrthonormalBasis ℝ (EC d)) B]
  simp only [map_sum,map_smul,smul_eq_mul,Complex.ofReal_sum,Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma cofactor_smooth_expression {U : EC d → ℝ} {y : EC d}
    (hU : ContDiffAt ℝ ∞ U y) (f : 𝓢(EC d,ℂ))
    (he : (f : EC d → ℂ) =ᶠ[𝓝 y] Complex.ofRealCLM ∘ U)
    (c : ℂ) (M : Matrix (Fin d) (Fin d) ℂ) :
    ((c * NonlinearHessian.detDifferential M (fun i j => hessianEntrySchwartz i j f y)).re : ℂ) =
      ∑ i, ∑ j, (cofactorBilin c M (rankTwo (stdOrthonormalBasis ℝ (EC d) i)
        (stdOrthonormalBasis ℝ (EC d) j)) : ℂ) *
        fderiv ℝ (fderiv ℝ f) y (stdOrthonormalBasis ℝ (EC d) i) (stdOrthonormalBasis ℝ (EC d) j) := by
  simp_rw [hessianEntrySchwartz_real hU f he]
  change (cofactorBilin c M (fderiv ℝ (fderiv ℝ U) y) : ℂ) = _
  rw [cofactorBilin_expansion]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [(he.fderiv (𝕜:=ℝ)).fderiv_eq,second_postcomp_general hU]
  rfl

end GlobalElliptic

end
end

end OAI
