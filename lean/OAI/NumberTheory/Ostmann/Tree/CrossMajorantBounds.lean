import OAI.NumberTheory.Ostmann.Tree.TwoPairModeBounds
import OAI.NumberTheory.Ostmann.Tree.TwoPairRatioEnergy

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

def unitMean (f : ZMod p → ℝ) : ℝ :=
  (Fintype.card (ZMod p)ˣ:ℝ)⁻¹*∑ y : (ZMod p)ˣ,f y

theorem crossMajorant_mean_small (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (L R : PairMode) (ν : MulChar (ZMod p) ℂ)
    (hσ : (σ:ZMod p)^2=1) (hτ : (τ:ZMod p)^2=1)
    (hg0 : g 0=0) (hg : l2Sq g≤1) (hh0 : h 0=0) (hh : l2Sq h≤1) :
    unitMean (crossMajorant g h σ τ L R ν) ≤
      100*((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))*
      ((correlationBound g:ℝ)^2+(correlationBound h:ℝ)^2+Real.sqrt (3/(p:ℝ))) := by
  have hp : (p:ℝ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have he : (Fintype.card (ZMod p)ˣ:ℝ)⁻¹*(∑ y : ZMod p,crossMajorant g h σ τ L R ν y)=
      ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))*
      ((Fintype.card (ZMod p)ˣ:ℝ)⁻¹^2*
        ∑ lam : (ZMod p)ˣ,∑ mu : (ZMod p)ˣ,l2Sq (twoPairConvolution g h σ τ L R ν lam mu)) := by
    simp only [crossMajorant,l2Sq,← Finset.mul_sum]
    rw [← sum_three_rotate (fun lam mu y => ‖twoPairConvolution g h σ τ L R ν lam mu y‖^2)]
    field_simp
  have hb : ((Fintype.card (ZMod p)ˣ:ℝ)⁻¹^2*
      ∑ lam : (ZMod p)ˣ,∑ mu : (ZMod p)ˣ,l2Sq (twoPairConvolution g h σ τ L R ν lam mu)) ≤
      100*((correlationBound g:ℝ)^2+(correlationBound h:ℝ)^2+Real.sqrt (3/(p:ℝ))) := by
    rw [twoPairConvolution_energy g h σ τ L R ν hg0 hh0]
    exact twoPair_mode_convolution_bound g h σ τ L R ν hσ hτ hg0 hg hh0 hh
  unfold unitMean
  calc
    _ ≤ (Fintype.card (ZMod p)ˣ:ℝ)⁻¹*(∑ y : ZMod p,crossMajorant g h σ τ L R ν y) :=
      mul_le_mul_of_nonneg_left (sum_units_le _ (crossMajorant_nonneg g h σ τ L R ν)) (by positivity)
    _ = _ := he
    _ ≤ ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))*
        (100*((correlationBound g:ℝ)^2+(correlationBound h:ℝ)^2+Real.sqrt (3/(p:ℝ)))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

theorem sum_difference_products (A B : ZMod p → ℝ) :
    (∑ y : ZMod p,∑ d : ZMod p,A d*B (d-y))=(∑ d,A d)*(∑ e,B e) := by
  rw [Finset.sum_comm,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.mul_sum]
  congr 1
  have hi : Function.Bijective (fun y : ZMod p => d-y) := by
    constructor
    · exact sub_right_injective
    · intro e
      exact ⟨d-e,by ring⟩
  exact hi.sum_comp B

theorem crossMajorant_mean_total (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (L R : PairMode) (hg0 : g 0=0) (hg : l2Sq g≤1) (hh0 : h 0=0) (hh : l2Sq h≤1) :
    (∑ ν : MulChar (ZMod p) ℂ,unitMean (crossMajorant g h σ τ L R ν)) ≤
      ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^2 := by
  have hp : (p:ℝ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hN : (Fintype.card (ZMod p)ˣ:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  let A := pairSecondMoment g σ
  let B := pairSecondMoment h τ
  have hA : ∀ d,0≤A d := pairSecondMoment_nonneg g σ
  have hB : ∀ d,0≤B d := pairSecondMoment_nonneg h τ
  have hconv (y : ZMod p) : 0≤∑ d : ZMod p,A d*B (d-y) :=
    Finset.sum_nonneg (fun d _ => mul_nonneg (hA d) (hB _))
  unfold unitMean
  rw [← Finset.mul_sum,Finset.sum_comm]
  simp_rw [crossMajorant_sum g h σ τ L R _ hg0 hh0]
  rw [← Finset.mul_sum]
  calc
    _ = (p:ℝ)⁻¹^2*∑ y : (ZMod p)ˣ,∑ d : ZMod p,A d*B (d-y) := by dsimp [A,B]; field_simp
    _ ≤ (p:ℝ)⁻¹^2*∑ y : ZMod p,∑ d : ZMod p,A d*B (d-y) :=
      mul_le_mul_of_nonneg_left (sum_units_le _ hconv) (sq_nonneg _)
    _ = (p:ℝ)⁻¹^2*((∑ d,A d)*(∑ e,B e)) := by rw [sum_difference_products]
    _ ≤ (p:ℝ)⁻¹^2*(((p:ℝ)^2/(Fintype.card (ZMod p)ˣ:ℝ))*((p:ℝ)^2/(Fintype.card (ZMod p)ˣ:ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact mul_le_mul (pairSecondMoment_total g σ hg0 hg) (pairSecondMoment_total h τ hh0 hh)
        (Finset.sum_nonneg (fun _ _ => hB _)) (by positivity)
    _ = _ := by field_simp

end
end Ostmann.FiniteField

end OAI
