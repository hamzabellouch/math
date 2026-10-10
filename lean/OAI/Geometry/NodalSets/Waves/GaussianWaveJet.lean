import OAI.Geometry.NodalSets.Coefficients.DualWaveCoefficient
import OAI.Geometry.NodalSets.Coefficients.GaussianCoefficientVariance
import OAI.Geometry.NodalSets.Elliptic.RealPhaseJet

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι]

def gaussianCoefficient (a : ι × Fin 2 → ℝ) (i : ι) : ℂ :=
  (a (i,0):ℂ)+Complex.I*(a (i,1):ℂ)

lemma pairLinearSum_eq_complex (z : ι → ℂ) (a : ι × Fin 2 → ℝ) :
    pairLinearSum z a = ∑ i, (gaussianCoefficient a i*z i).re := by
  classical
  simp only [pairLinearSum,Fintype.sum_prod_type,Fin.sum_univ_succ,Fin.succ_ne_zero,Fin.succ_zero_eq_one,ite_true,ite_false,Fin.sum_univ_zero,add_zero,
    gaussianCoefficient,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,mul_zero,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  ring

def gaussianWaveField (V : ι → Coord → ℂ) (a : ι × Fin 2 → ℝ) (x : Coord) : ℝ :=
  (∑ i, gaussianCoefficient a i*V i x).re

lemma gaussianWaveField_dual (V : ι → Coord → ℂ) (a : ι × Fin 2 → ℝ)
    (x v : Coord) (hV : ∀ i, DifferentiableAt ℝ (V i) x) (N S b : ℝ) :
    Real.exp (-N*S)*(b*gaussianWaveField V a x+N⁻¹*fderiv ℝ (gaussianWaveField V a) x v) =
      pairLinearSum (fun i ↦ dualWaveCoefficient N (V i) S x b v) a := by
  classical
  let W : Coord → ℂ := fun z ↦ ∑ i, gaussianCoefficient a i*V i z
  have hW : DifferentiableAt ℝ W x := DifferentiableAt.fun_sum (fun i _ ↦ (hV i).const_mul _)
  have hd : fderiv ℝ W x v = ∑ i, gaussianCoefficient a i*fderiv ℝ (V i) x v := by
    dsimp only [W]
    rw [fderiv_fun_sum (fun i _ ↦ (hV i).const_mul _)]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [((hV i).hasFDerivAt.const_mul (gaussianCoefficient a i)).fderiv]
    rfl
  have hr := realPart_fderiv W x hW v
  change fderiv ℝ (gaussianWaveField V a) x v = _ at hr
  rw [hr,hd,pairLinearSum_eq_complex]
  simp only [gaussianWaveField,Complex.re_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [dualWaveCoefficient,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,← Complex.ofReal_inv,
    zero_mul,sub_zero,add_zero]
  ring

end
end Yau.Geometry

end OAI
