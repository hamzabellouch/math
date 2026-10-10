import OAI.NumberTheory.Ostmann.Tree.BadNonprincipalConvolution
import OAI.NumberTheory.Ostmann.Tree.BadPrincipalConvolution
import OAI.NumberTheory.Ostmann.Tree.CorrelationSymmetry

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

theorem bad_convolution_precise (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (ν : MulChar (ZMod p) ℂ) (hg0 : g 0=0) (hg : l2Sq g≤1)
    (hh0 : h 0=0) (hh : l2Sq h≤1) :
    (∑ χ : MulChar (ZMod p) ℂ,∑ ψ : MulChar (ZMod p) ℂ,∑ a : ZMod p,
      ‖twistedPairFourier g σ χ (ν*ψ⁻¹) a‖^2*
      ‖twistedPairFourier h τ ψ (ν⁻¹*χ⁻¹) (-a)‖^2) ≤
      ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^3*
        (2*(correlationBound g:ℝ)^2+2*(correlationBound h:ℝ)^2+7/(p:ℝ))+
      (((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))*(correlationBound g:ℝ)^2+
        (Fintype.card (ZMod p)ˣ:ℝ)⁻¹)^2 *
      ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^2 := by
  have hn := bad_nonprincipal_convolution_bound g h σ τ ν hg0 hg hh0 hh
  have hl := bad_mixed_left_bound g h σ τ ν hg0 hg hh0 hh
  have hr := bad_mixed_right_bound g h σ τ ν hg0 hg hh0 hh
  have hp := bad_principal_bound g h σ τ ν hg0 hg hh0 hh
  simp_rw [spectralEnergy_decomposition,add_mul,mul_add,Finset.sum_add_distrib]
  simp only [div_eq_mul_inv] at hn hl hr hp ⊢
  nlinarith only [hn,hl,hr,hp]

theorem prime_unit_ratio_le_two : (p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ)≤2 := by
  have hp : (2:ℝ)≤p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hN : 0<(Fintype.card (ZMod p)ˣ:ℝ) := by exact_mod_cast Fintype.card_pos
  have he : (Fintype.card (ZMod p)ˣ:ℝ)=(p:ℝ)-1 := by
    rw [ZMod.card_units,Nat.cast_sub (Fact.out : p.Prime).one_lt.le,Nat.cast_one]
  apply (div_le_iff₀ hN).mpr
  rw [he]
  linarith

theorem bad_convolution_bound (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (ν : MulChar (ZMod p) ℂ) (hg0 : g 0=0) (hg : l2Sq g≤1)
    (hh0 : h 0=0) (hh : l2Sq h≤1) :
    (∑ χ : MulChar (ZMod p) ℂ,∑ ψ : MulChar (ZMod p) ℂ,∑ a : ZMod p,
      ‖twistedPairFourier g σ χ (ν*ψ⁻¹) a‖^2*
      ‖twistedPairFourier h τ ψ (ν⁻¹*χ⁻¹) (-a)‖^2) ≤
      100*((correlationBound g:ℝ)^2+(correlationBound h:ℝ)^2+(p:ℝ)⁻¹) := by
  let C : ℝ := (p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ)
  let x : ℝ := (correlationBound g:ℝ)^2
  let y : ℝ := (correlationBound h:ℝ)^2
  let t : ℝ := (p:ℝ)⁻¹
  have hC0 : 0≤C := by dsimp [C]; positivity
  have hC2 : C≤2 := prime_unit_ratio_le_two
  have hx0 : 0≤x := sq_nonneg _
  have hy0 : 0≤y := sq_nonneg _
  have hx1 : x≤1 := by
    exact (pow_le_pow_left₀ (NNReal.coe_nonneg _) (correlationBound_le_one g hg) 2).trans_eq (by norm_num)
  have ht0 : 0≤t := by dsimp [t]; positivity
  have ht1 : t≤1 := by
    dsimp [t]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  have hC3 : C^3≤8 := (pow_le_pow_left₀ hC0 hC2 3).trans_eq (by norm_num)
  have hC4 : C^4≤16 := (pow_le_pow_left₀ hC0 hC2 4).trans_eq (by norm_num)
  have hs : (x+t)^2≤2*x+2*t := by
    have hx := mul_le_mul_of_nonneg_left hx1 hx0
    have ht := mul_le_mul_of_nonneg_left ht1 ht0
    nlinarith only [hx,ht,sq_nonneg (x-t)]
  have hprec := bad_convolution_precise g h σ τ ν hg0 hg hh0 hh
  have hp : (p:ℝ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hform :
      C^3*(2*x+2*y+7/(p:ℝ))+
        (C*x+(Fintype.card (ZMod p)ˣ:ℝ)⁻¹)^2*C^2 =
      C^3*(2*x+2*y+7*t)+C^4*(x+t)^2 := by
    dsimp [C,t]
    field_simp
  change _≤C^3*(2*x+2*y+7/(p:ℝ))+(C*x+(Fintype.card (ZMod p)ˣ:ℝ)⁻¹)^2*C^2 at hprec
  rw [hform] at hprec
  have hfirst := mul_le_mul_of_nonneg_right hC3 (show 0≤2*x+2*y+7*t by positivity)
  have hsecond := mul_le_mul hC4 hs (sq_nonneg _) (by norm_num : (0:ℝ)≤16)
  change _≤100*(x+y+t)
  nlinarith only [hprec,hfirst,hsecond,hx0,hy0,ht0]

end
end Ostmann.FiniteField

end OAI
