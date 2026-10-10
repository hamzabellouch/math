import OAI.Analysis.Cotype.ComplexPowerGapInverse
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Normed.Operator.Mul

namespace OAI

noncomputable section
namespace Cotype
open MeasureTheory
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def exponentialIntegral (L : A) (t : ℝ) : A :=
  ∫ s in (0 : ℝ)..t, NormedSpace.exp (s • L)

theorem exponentialIntegral_mul (L : A) (t : ℝ) :
    exponentialIntegral L t * L = NormedSpace.exp (t • L) - 1 := by
  have hf := (differentiable_exp_smul_const ℝ L).continuous
  have hint := hf.intervalIntegrable (μ := volume) (0 : ℝ) t
  have hm := (ContinuousLinearMap.mulLeftRight ℝ A 1 L).intervalIntegral_comp_comm hint
  simp only [ContinuousLinearMap.mulLeftRight_apply, one_mul] at hm
  rw [exponentialIntegral, ← hm]
  simpa only [zero_smul, NormedSpace.exp_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hasDerivAt_exp_smul_const L s)
      ((hf.mul continuous_const).intervalIntegrable (0 : ℝ) t)

theorem mul_exponentialIntegral (L : A) (t : ℝ) :
    L * exponentialIntegral L t = NormedSpace.exp (t • L) - 1 := by
  have hf := (differentiable_exp_smul_const ℝ L).continuous
  have hint := hf.intervalIntegrable (μ := volume) (0 : ℝ) t
  have hm := (ContinuousLinearMap.mulLeftRight ℝ A L 1).intervalIntegral_comp_comm hint
  simp only [ContinuousLinearMap.mulLeftRight_apply, mul_one] at hm
  rw [exponentialIntegral, ← hm]
  simpa only [zero_smul, NormedSpace.exp_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hasDerivAt_exp_smul_const' L s)
      ((continuous_const.mul hf).intervalIntegrable (0 : ℝ) t)

omit [NormedAlgebra ℝ A] [CompleteSpace A] in

theorem exists_inverse_of_commuting_factorization (L V : A) (U : Aˣ)
    (hleft : L*V = (U : A)) (hright : V*L = (U : A)) :
    ∃ W : Aˣ, (W : A) = L ∧ ‖(↑W⁻¹ : A)‖ ≤ ‖V‖ * ‖(↑U⁻¹ : A)‖ := by
  have huv : (U : A) * (↑U⁻¹ : A) = 1 := U.val_inv
  have huiv : (↑U⁻¹ : A) * (U : A) = 1 := U.inv_val
  have hr : L * (V * (↑U⁻¹ : A)) = 1 := by rw [← mul_assoc, hleft, huv]
  have hl : ((↑U⁻¹ : A) * V) * L = 1 := by rw [mul_assoc, hright, huiv]
  have heq : (↑U⁻¹ : A) * V = V * (↑U⁻¹ : A) := by
    calc
      _ = ((↑U⁻¹ : A) * V) * (L * (V * (↑U⁻¹ : A))) := by rw [hr, mul_one]
      _ = V * (↑U⁻¹ : A) := by rw [← mul_assoc, hl, one_mul]
  refine ⟨⟨L, V * (↑U⁻¹ : A), hr, ?_⟩, rfl, norm_mul_le _ _⟩
  rw [← heq, hl]

end Cotype

end

end OAI
