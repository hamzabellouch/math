import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTangentIsometry
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

/-! The squared differential norm is independent of the orthonormal
tangent frame. This is the complex-valued Dirichlet energy, expressed
as the sum of the real and imaginary dual norms. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaTangentBasis := stdOrthonormalBasis ℝ CubicThetaTangent

def cubicThetaTangentEnergy (L : CubicThetaTangent →L[ℝ] ℂ) : ℝ :=
  ∑ i, ‖L (cubicThetaTangentBasis i)‖^2

lemma cubicThetaTangentEnergy_basis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ CubicThetaTangent) (L : CubicThetaTangent →L[ℝ] ℂ) :
    (∑ i, ‖L (b i)‖^2)=‖Complex.reCLM.comp L‖^2+‖Complex.imCLM.comp L‖^2 := by
  rw [b.norm_dual (Complex.reCLM.comp L),b.norm_dual (Complex.imCLM.comp L),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [ContinuousLinearMap.comp_apply,Complex.reCLM_apply,Complex.imCLM_apply,
    ← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  ring

lemma cubicThetaTangentEnergy_isometry (L : CubicThetaTangent →L[ℝ] ℂ)
    (J : CubicThetaTangent ≃ₗᵢ[ℝ] CubicThetaTangent) :
    cubicThetaTangentEnergy (L.comp J.toContinuousLinearEquiv.toContinuousLinearMap)=
      cubicThetaTangentEnergy L := by
  change (∑ i, ‖L ((cubicThetaTangentBasis.map J) i)‖^2)=_
  rw [cubicThetaTangentEnergy_basis]
  exact (cubicThetaTangentEnergy_basis cubicThetaTangentBasis L).symm

lemma cubicThetaTangentEnergy_real_smul (r : ℝ) (L : CubicThetaTangent →L[ℝ] ℂ) :
    cubicThetaTangentEnergy (r • L)=r^2*cubicThetaTangentEnergy L := by
  simp only [cubicThetaTangentEnergy,smul_apply,norm_smul,
    mul_pow,Real.norm_eq_abs,sq_abs,Finset.mul_sum]

lemma cubicThetaTangentEnergy_complex_smul (c : ℂ) (L : CubicThetaTangent →L[ℝ] ℂ) :
    cubicThetaTangentEnergy (c • L)=‖c‖^2*cubicThetaTangentEnergy L := by
  simp only [cubicThetaTangentEnergy,smul_apply,norm_smul,
    mul_pow,Finset.mul_sum]

lemma cubicThetaTangentEnergy_derivative (L : CubicThetaTangent →L[ℝ] ℂ)
    (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaTangentEnergy (L.comp (cubicThetaTangentDerivative g p))=
      ((cubicThetaMobius g p).2/p.2)^2*cubicThetaTangentEnergy L := by
  have he : L.comp (cubicThetaTangentDerivative g p)=
      ((cubicThetaMobius g p).2/p.2) •
        (L.comp (cubicThetaTangentIsometry g hp).toContinuousLinearEquiv.toContinuousLinearMap) := by
    ext u
    simp only [ContinuousLinearMap.comp_apply,smul_apply,
      ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [cubicThetaTangentDerivative_eq g hp,L.map_smul]
  rw [he,cubicThetaTangentEnergy_real_smul,cubicThetaTangentEnergy_isometry]

end CubicFirstMoment

end

end OAI
