import OAI.NumberTheory.Ostmann.Tree.DeletedPairEnergy

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]

def samePairMajorant (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (ρ : MulChar (ZMod p) ℂ) : ZMod p → ℝ :=
  nonnegativeDifference (pairSquareEnergy g σ ρ) (pairSecondMoment h τ)

def untouchedMajorant (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ) : ZMod p → ℝ :=
  nonnegativeDifference (pairSecondMoment g σ) (pairSecondMoment h τ)

theorem samePairMajorant_nonneg (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) : 0 ≤ samePairMajorant g h σ τ ρ y :=
  nonnegativeDifference_nonneg _ _ (pairSquareEnergy_nonneg g σ ρ) (pairSecondMoment_nonneg h τ) y

theorem untouchedMajorant_nonneg (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (y : ZMod p) : 0≤untouchedMajorant g h σ τ y :=
  nonnegativeDifference_nonneg _ _ (pairSecondMoment_nonneg g σ) (pairSecondMoment_nonneg h τ) y

theorem samePairMajorant_mean_bound (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (ρ : MulChar (ZMod p) ℂ) (hh0 : h 0=0) (hh : l2Sq h≤1) :
    unitMean (samePairMajorant g h σ τ ρ) ≤
      ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^3*
        ∑ χ : MulChar (ZMod p) ℂ with χ^2=ρ,pairFourthMass g χ := by
  classical
  have hN : (Fintype.card (ZMod p)ˣ:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  apply (nonnegativeDifference_mean _ _ (pairSquareEnergy_nonneg g σ ρ) (pairSecondMoment_nonneg h τ)).trans
  calc
    _ ≤ (Fintype.card (ZMod p)ˣ:ℝ)⁻¹^2*
        (((p:ℝ)*∑ χ : MulChar (ZMod p) ℂ with χ^2=ρ,pairFourthMass g χ)*
          ((p:ℝ)^2/(Fintype.card (ZMod p)ˣ:ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact mul_le_mul (pairSquareEnergy_total g σ ρ) (pairSecondMoment_total h τ hh0 hh)
        (Finset.sum_nonneg (fun d _ => pairSecondMoment_nonneg h τ d))
        (mul_nonneg (by positivity) (Finset.sum_nonneg (fun χ _ => by unfold pairFourthMass; positivity)))
    _ = _ := by field_simp

theorem samePairMajorant_mean_small (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (ρ : MulChar (ZMod p) ℂ) (hg0 : g 0=0) (hg : l2Sq g≤1)
    (hh0 : h 0=0) (hh : l2Sq h≤1) :
    unitMean (samePairMajorant g h σ τ ρ) ≤
      2*((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^5*(correlationBound g:ℝ)^2 := by
  apply (samePairMajorant_mean_bound g h σ τ ρ hh0 hh).trans
  apply (mul_le_mul_of_nonneg_left (pairFourthMass_square_fiber g ρ hg0 hg) (by positivity)).trans_eq
  ring

theorem samePairMajorant_mean_total (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (hg0 : g 0=0) (hg : l2Sq g≤1) (hh0 : h 0=0) (hh : l2Sq h≤1) :
    (∑ ρ : MulChar (ZMod p) ℂ,unitMean (samePairMajorant g h σ τ ρ)) ≤
      2*((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^4 := by
  classical
  calc
    _ ≤ ∑ ρ : MulChar (ZMod p) ℂ,((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^3*
        ∑ χ : MulChar (ZMod p) ℂ with χ^2=ρ,pairFourthMass g χ :=
      Finset.sum_le_sum (fun ρ _ => samePairMajorant_mean_bound g h σ τ ρ hh0 hh)
    _ = ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^3*∑ χ : MulChar (ZMod p) ℂ,pairFourthMass g χ := by
      rw [← Finset.mul_sum]
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      simp
    _ ≤ ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^3*(2*(p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ)) :=
      mul_le_mul_of_nonneg_left (pairFourthMass_total g hg0 hg) (by positivity)
    _ = _ := by ring

theorem untouchedMajorant_mean (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (hg0 : g 0=0) (hg : l2Sq g≤1) (hh0 : h 0=0) (hh : l2Sq h≤1) :
    unitMean (untouchedMajorant g h σ τ) ≤ ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^4 := by
  have hN : (Fintype.card (ZMod p)ˣ:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  apply (nonnegativeDifference_mean _ _ (pairSecondMoment_nonneg g σ) (pairSecondMoment_nonneg h τ)).trans
  calc
    _ ≤ (Fintype.card (ZMod p)ˣ:ℝ)⁻¹^2*
        (((p:ℝ)^2/(Fintype.card (ZMod p)ˣ:ℝ))*((p:ℝ)^2/(Fintype.card (ZMod p)ˣ:ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact mul_le_mul (pairSecondMoment_total g σ hg0 hg) (pairSecondMoment_total h τ hh0 hh)
        (Finset.sum_nonneg (fun d _ => pairSecondMoment_nonneg h τ d)) (by positivity)
    _ = _ := by field_simp

end
end Ostmann.FiniteField

end OAI
