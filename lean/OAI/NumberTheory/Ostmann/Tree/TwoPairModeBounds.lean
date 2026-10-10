import OAI.NumberTheory.Ostmann.Tree.BadConvolution
import OAI.NumberTheory.Ostmann.Tree.FriendlyRightConvolution
import OAI.NumberTheory.Ostmann.Tree.TwoPairMellin

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

theorem friendly_constant_bound (g h : ZMod p → ℂ) (hg : l2Sq g≤1) :
    (2*((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^2)*
      ((correlationBound g:ℝ)^4+Real.sqrt (3/(p:ℝ))) ≤
    100*((correlationBound g:ℝ)^2+(correlationBound h:ℝ)^2+Real.sqrt (3/(p:ℝ))) := by
  have hr : ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^2≤4 :=
    (pow_le_pow_left₀ (show (0:ℝ)≤(p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ) by positivity)
      (prime_unit_ratio_le_two (p:=p)) 2).trans_eq (by norm_num)
  have he : (correlationBound g:ℝ)^2≤1 :=
    (pow_le_pow_left₀ (NNReal.coe_nonneg (correlationBound g)) (correlationBound_le_one g hg) 2).trans_eq (by norm_num)
  have he4 : (correlationBound g:ℝ)^4≤(correlationBound g:ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_left he (sq_nonneg (correlationBound g:ℝ))
    nlinarith only [hh]
  have hprod := mul_le_mul (show 2*((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^2≤8 by linarith)
    (add_le_add he4 le_rfl) (show 0≤(correlationBound g:ℝ)^4+Real.sqrt (3/(p:ℝ)) by positivity)
    (show (0:ℝ)≤8 by norm_num)
  nlinarith only [hprod,sq_nonneg (correlationBound g:ℝ),sq_nonneg (correlationBound h:ℝ),Real.sqrt_nonneg (3/(p:ℝ))]

theorem inv_prime_le_sqrt_three : (p:ℝ)⁻¹≤Real.sqrt (3/(p:ℝ)) := by
  have hp : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have ht : (p:ℝ)⁻¹≤1 := inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  have hz : 0≤(p:ℝ)⁻¹ := inv_nonneg.mpr hp.le
  have hs := Real.sq_sqrt (show (0:ℝ)≤3/(p:ℝ) by positivity)
  have hm := mul_le_mul_of_nonneg_left ht hz
  have hsp := Real.sqrt_nonneg (3/(p:ℝ))
  simp only [div_eq_mul_inv] at hs hsp ⊢
  nlinarith only [hm,hs,hsp,hz]

theorem twoPair_mode_convolution_bound (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (L R : PairMode) (ν : MulChar (ZMod p) ℂ)
    (hσ : (σ:ZMod p)^2=1) (hτ : (τ:ZMod p)^2=1)
    (hg0 : g 0=0) (hg : l2Sq g≤1) (hh0 : h 0=0) (hh : l2Sq h≤1) :
    (∑ χ : MulChar (ZMod p) ℂ,∑ ψ : MulChar (ZMod p) ℂ,∑ a : ZMod p,
      ‖twistedPairFourier g σ χ (leftPairTwist L R ν χ ψ) a‖^2 *
      ‖twistedPairFourier h τ ψ (rightPairTwist L R ν χ ψ) (-a)‖^2) ≤
    100*((correlationBound g:ℝ)^2+(correlationBound h:ℝ)^2+Real.sqrt (3/(p:ℝ))) := by
  have hcycle (F : MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ → ZMod p → ℝ) :
      (∑ χ,∑ ψ,∑ a,F χ ψ a)=∑ ψ,∑ a,∑ χ,F χ ψ a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ψ _
    rw [Finset.sum_comm]
  have hswap (F : MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ → ZMod p → ℝ) :
      (∑ χ,∑ ψ,∑ a,F χ ψ a)=∑ χ,∑ a,∑ ψ,F χ ψ a := by
    apply Finset.sum_congr rfl
    intro χ _
    rw [Finset.sum_comm]
  cases L <;> cases R
  · rw [hcycle]
    have he := friendly_convolution_bound g h σ τ hσ hg0 hg hh0 hh
      (fun _ => ν) (fun ψ => ν⁻¹*ψ)
    apply le_trans _ (friendly_constant_bound g h hg)
    simpa only [leftPairTwist,rightPairTwist,mul_one,mul_comm] using he
  · rw [hcycle]
    have he := friendly_convolution_bound g h σ τ hσ hg0 hg hh0 hh
      (fun ψ => ν*ψ⁻¹) (fun _ => ν⁻¹)
    apply le_trans _ (friendly_constant_bound g h hg)
    simpa only [leftPairTwist,rightPairTwist,mul_one,mul_assoc,mul_comm,mul_left_comm,add_comm] using he
  · rw [hswap]
    have he := friendly_convolution_right_bound g h σ τ hτ hg0 hg hh0 hh
      (fun _ => ν) (fun χ => ν⁻¹*χ⁻¹)
    apply le_trans _ (show _≤100*((correlationBound g:ℝ)^2+(correlationBound h:ℝ)^2+Real.sqrt (3/(p:ℝ))) from by
      simpa only [add_comm,add_left_comm,add_assoc] using friendly_constant_bound h g hh)
    simpa only [leftPairTwist,rightPairTwist,mul_one,mul_assoc,mul_comm,mul_left_comm,add_comm] using he
  · have he := bad_convolution_bound g h σ τ ν hg0 hg hh0 hh
    apply le_trans _ (mul_le_mul_of_nonneg_left (add_le_add le_rfl (inv_prime_le_sqrt_three (p:=p))) (by norm_num : (0:ℝ)≤100))
    simpa only [leftPairTwist,rightPairTwist,mul_one] using he

end
end Ostmann.FiniteField

end OAI
