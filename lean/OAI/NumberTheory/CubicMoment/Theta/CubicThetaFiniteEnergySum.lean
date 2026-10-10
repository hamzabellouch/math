import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFunctionEnergyTransport
import Mathlib.Algebra.Order.Chebyshev

namespace OAI

/-! A finite sum estimate for the literal squared differential norm. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaTangentEnergy_sum_le {ι : Type*} (S : Finset ι)
    (L : ι → CubicThetaTangent →L[ℝ] ℂ) :
    cubicThetaTangentEnergy (∑ i∈S,L i)≤
      (S.card:ℝ)*∑ i∈S,cubicThetaTangentEnergy (L i) := by
  classical
  unfold cubicThetaTangentEnergy
  calc
    _ ≤ ∑ j, (S.card:ℝ)*∑ i∈S,‖L i (cubicThetaTangentBasis j)‖^2 := by
      apply Finset.sum_le_sum
      intro j _
      simp only [sum_apply]
      have hsq := mul_self_le_mul_self (_root_.norm_nonneg _) (norm_sum_le S
        (fun i => L i (cubicThetaTangentBasis j)))
      rw [← pow_two,← pow_two] at hsq
      exact hsq.trans (sq_sum_le_card_mul_sum_sq (s:=S)
        (f:=fun i => ‖L i (cubicThetaTangentBasis j)‖))
    _ = _ := by
      rw [← Finset.mul_sum,Finset.sum_comm]

lemma cubicThetaFunctionEnergy_sum_le {ι : Type*} (S : Finset ι)
    (f : ι → ℂ × ℝ → ℂ) (p : ℂ × ℝ)
    (hf : ∀ i∈S,DifferentiableAt ℝ (f i) p) :
    cubicThetaFunctionEnergy (fun y => ∑ i∈S,f i y) p≤
      (S.card:ℝ)*∑ i∈S,cubicThetaFunctionEnergy (f i) p := by
  have he : (fderiv ℝ (fun y => ∑ i∈S,f i y) p).comp cubicThetaTangentCoordinates.toContinuousLinearMap=
      ∑ i∈S,(fderiv ℝ (f i) p).comp cubicThetaTangentCoordinates.toContinuousLinearMap := by
    rw [fderiv_fun_sum hf]
    ext u
    simp only [ContinuousLinearMap.comp_apply,sum_apply]
  unfold cubicThetaFunctionEnergy
  rw [he]
  exact cubicThetaTangentEnergy_sum_le S _

lemma cubicThetaFunctionEnergy_one_sub {f : ℂ × ℝ → ℂ} {p : ℂ × ℝ}
    (hf : DifferentiableAt ℝ f p) :
    cubicThetaFunctionEnergy (fun y => 1-f y) p=cubicThetaFunctionEnergy f p := by
  have he : fderiv ℝ (fun y => 1-f y) p= -(fderiv ℝ f p) := by
    rw [fderiv_fun_sub (differentiableAt_const _) hf,fderiv_const_apply,zero_sub]
  simp only [cubicThetaFunctionEnergy,he,cubicThetaTangentEnergy,
    ContinuousLinearMap.comp_apply,neg_apply,norm_neg]

end CubicFirstMoment

end

end OAI
