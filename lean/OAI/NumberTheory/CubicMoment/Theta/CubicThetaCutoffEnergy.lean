import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEnergyCoordinates
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLocalEnergyJet

namespace OAI

/-! Quantitative product estimates for the compact core cutoffs.
The coefficient is compactly supported, so its supremum is finite. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma cubicThetaTangentEnergy_nonneg (L : CubicThetaTangent →L[ℝ] ℂ) :
    0≤cubicThetaTangentEnergy L := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma cubicThetaTangentEnergy_add_le (L M : CubicThetaTangent →L[ℝ] ℂ) :
    cubicThetaTangentEnergy (L+M)≤2*cubicThetaTangentEnergy L+2*cubicThetaTangentEnergy M := by
  unfold cubicThetaTangentEnergy
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  simp only [add_apply]
  have ht := norm_add_le (L (cubicThetaTangentBasis i)) (M (cubicThetaTangentBasis i))
  have hs := mul_self_le_mul_self (_root_.norm_nonneg _) ht
  nlinarith [sq_nonneg (‖L (cubicThetaTangentBasis i)‖-‖M (cubicThetaTangentBasis i)‖)]

def cubicThetaFunctionEnergy (f : ℂ × ℝ → ℂ) (y : ℂ × ℝ) : ℝ :=
  cubicThetaTangentEnergy ((fderiv ℝ f y).comp cubicThetaTangentCoordinates.toContinuousLinearMap)

lemma cubicThetaFunctionEnergy_mul {f g : ℂ × ℝ → ℂ} {y : ℂ × ℝ}
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    cubicThetaFunctionEnergy (f*g) y≤
      2*‖f y‖^2*cubicThetaFunctionEnergy g y+2*‖g y‖^2*cubicThetaFunctionEnergy f y := by
  have he : ((fderiv ℝ (f*g) y).comp cubicThetaTangentCoordinates.toContinuousLinearMap)=
      f y • ((fderiv ℝ g y).comp cubicThetaTangentCoordinates.toContinuousLinearMap)+
        g y • ((fderiv ℝ f y).comp cubicThetaTangentCoordinates.toContinuousLinearMap) := by
    rw [fderiv_mul hf hg]
    ext u
    simp only [ContinuousLinearMap.comp_apply,add_apply,smul_apply]
  unfold cubicThetaFunctionEnergy
  rw [he]
  exact (cubicThetaTangentEnergy_add_le _ _).trans_eq (by
    rw [cubicThetaTangentEnergy_complex_smul,cubicThetaTangentEnergy_complex_smul]
    ring)

lemma cubicThetaLocalEnergyJet_density (f : ℂ × ℝ → ℂ) {y : ℂ × ℝ} (hy : 0<y.2) :
    ‖cubicThetaLocalEnergyJet f y‖^2=
      (‖f y‖^2+y.2^2*cubicThetaFunctionEnergy f y)/y.2^3 := by
  rw [cubicThetaLocalEnergyJet_norm_sq f hy]
  unfold cubicThetaFunctionEnergy
  rw [cubicThetaTangentEnergy_coordinates]
  field_simp [hy.ne']

def cubicThetaCutoffEnergyCoefficient (φ : ℂ × ℝ → ℂ) (y : ℂ × ℝ) : ℝ :=
  2*‖φ y‖^2+2*y.2^2*cubicThetaFunctionEnergy φ y

lemma cubicThetaCutoffEnergyCoefficient_nonneg (φ : ℂ × ℝ → ℂ) (y : ℂ × ℝ) :
    0≤cubicThetaCutoffEnergyCoefficient φ y :=
  add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (cubicThetaTangentEnergy_nonneg _))

lemma cubicThetaLocalEnergyJet_cutoff_le {φ f : ℂ × ℝ → ℂ} {y : ℂ × ℝ}
    (hy : 0<y.2) (hφ : DifferentiableAt ℝ φ y) (hf : DifferentiableAt ℝ f y) :
    ‖cubicThetaLocalEnergyJet (φ*f) y‖^2≤
      cubicThetaCutoffEnergyCoefficient φ y*‖cubicThetaLocalEnergyJet f y‖^2 := by
  rw [cubicThetaLocalEnergyJet_density _ hy,cubicThetaLocalEnergyJet_density _ hy,
    ← mul_div_assoc]
  apply (div_le_div_iff_of_pos_right (pow_pos hy 3)).mpr
  have he := cubicThetaFunctionEnergy_mul hφ hf
  have hEφ := cubicThetaTangentEnergy_nonneg
    ((fderiv ℝ φ y).comp cubicThetaTangentCoordinates.toContinuousLinearMap)
  have hEf := cubicThetaTangentEnergy_nonneg
    ((fderiv ℝ f y).comp cubicThetaTangentCoordinates.toContinuousLinearMap)
  change 0≤cubicThetaFunctionEnergy φ y at hEφ
  change 0≤cubicThetaFunctionEnergy f y at hEf
  have hmul := mul_le_mul_of_nonneg_left he (sq_nonneg y.2)
  simp only [Pi.mul_apply,norm_mul,mul_pow]
  unfold cubicThetaCutoffEnergyCoefficient
  nlinarith [mul_nonneg (sq_nonneg ‖φ y‖) (sq_nonneg ‖f y‖),
    mul_nonneg (sq_nonneg y.2) (mul_nonneg hEφ hEf)]

lemma cubicThetaFunctionEnergy_continuous {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) :
    Continuous (cubicThetaFunctionEnergy φ) := by
  unfold cubicThetaFunctionEnergy cubicThetaTangentEnergy
  apply continuous_finsetSum
  intro i hi
  exact (((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).norm).pow 2

lemma cubicThetaFunctionEnergy_compact {φ : ℂ × ℝ → ℂ} (hφ : HasCompactSupport φ) :
    HasCompactSupport (cubicThetaFunctionEnergy φ) := by
  apply hφ.mono'
  intro y hy
  by_contra hn
  have hd := fderiv_of_notMem_tsupport (𝕜:=ℝ) hn
  apply hy
  simp only [cubicThetaFunctionEnergy,hd,ContinuousLinearMap.zero_comp,
    cubicThetaTangentEnergy,zero_apply,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),
    Finset.sum_const_zero]

lemma cubicThetaCutoffEnergyCoefficient_bounded {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    ∃ C≥0, ∀ y, cubicThetaCutoffEnergyCoefficient φ y≤C := by
  have hcont : Continuous (cubicThetaCutoffEnergyCoefficient φ) :=
    (continuous_const.mul (hφ.continuous.norm.pow 2)).add
      ((continuous_const.mul (continuous_snd.pow 2)).mul (cubicThetaFunctionEnergy_continuous hφ))
  have hcompact : HasCompactSupport (cubicThetaCutoffEnergyCoefficient φ) :=
    ((hc.comp_left (g:=fun z : ℂ => ‖z‖^2) (by simp)).mul_left).add
      ((cubicThetaFunctionEnergy_compact hc).mul_left)
  obtain ⟨C,hC⟩ := hcompact.exists_bound_of_continuous hcont
  refine ⟨max C 0,le_max_right _ _,fun y => ?_⟩
  exact (le_abs_self _).trans ((hC y).trans (le_max_left _ _))

end CubicFirstMoment

end

end OAI
