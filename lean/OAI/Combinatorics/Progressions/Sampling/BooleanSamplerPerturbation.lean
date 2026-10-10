import OAI.Combinatorics.Progressions.Estimates.BooleanSelectedDerivativeBound

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem boolean_selected_inverse_perturbation {B O α : Type*}
    [Fintype B] [Fintype O] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (hblock : Function.Injective block)
    {h : ℕ} (v : Fin h) (r : O → Option α) (hcard : ∀ o, (sets o).card ≤ h)
    (a : BlockParameter B (Fin h) α → ℝ) {C R κ : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hc : ∀ o, |c (block o)| ≤ C) (ha : ∀ j, |a j| ≤ R)
    (hκ : 0 < κ)
    (hdet : κ ≤ |((booleanSelectedMinor c sets block v r).map (MvPolynomial.eval a)).det|)
    (V : (BlockParameter B (Fin h) α → ℝ) → (O → ℝ))
    (hsmall : productMinorInverseBound (Fintype.card O) (Fintype.card α) h C R κ *
      ‖fderiv ℝ V a - fderiv ℝ (booleanSamplerMap c sets) a‖ ≤ 1 / 2) :
    (selectedDerivative V (booleanSelectedInjection block v r) a).IsInvertible ∧
      ‖(selectedDerivative V (booleanSelectedInjection block v r) a).inverse‖ ≤
        2 * productMinorInverseBound (Fintype.card O) (Fintype.card α) h C R κ := by
  let K : ℝ≥0 := ⟨productMinorInverseBound (Fintype.card O) (Fintype.card α) h C R κ,
    productMinorInverseBound_nonneg _ _ _ hC hR hκ.le⟩
  obtain ⟨hinv, hbound⟩ := boolean_selected_inverse_bound c sets block v r hcard a hC hR hc ha hκ hdet
  have hJ := booleanSelectedInjection_norm_le block hblock v r
  have hsmall' : (K : ℝ) * (‖fderiv ℝ V a - fderiv ℝ (booleanSamplerMap c sets) a‖ *
      ‖booleanSelectedInjection block v r‖) ≤ 1 / 2 := by
    apply le_trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hJ (norm_nonneg _)) K.coe_nonneg)
    simp only [mul_one]
    exact hsmall
  exact selected_inverse_perturbation (booleanSamplerMap c sets) V
    (booleanSelectedInjection block v r) a hinv K hbound hsmall'

end Erdos3

end

end OAI
