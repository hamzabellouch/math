import OAI.NumberTheory.TwoPoint.Halasz.HalaszTorusBessel
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! Translation of the localized Fourier kernel on the coefficient torus. -/
namespace TwoPointCorrelations

open MeasureTheory Finset
open scoped ComplexConjugate

lemma halasz_character_argument_add {k : ℕ} (m : Fin k → ℤ)
    (α β : Fin k → AddCircle (1:ℝ)) :
    halaszVinogradovCharacter m (α+β)=
      halaszVinogradovCharacter m α*halaszVinogradovCharacter m β := by
  simp only [halaszVinogradovCharacter,Pi.add_apply,fourier_apply,zsmul_add,
    AddCircle.toCircle_add,Circle.coe_mul,prod_mul_distrib]

lemma halasz_character_argument_neg {k : ℕ} (m : Fin k → ℤ)
    (α : Fin k → AddCircle (1:ℝ)) :
    halaszVinogradovCharacter m (-α)=conj (halaszVinogradovCharacter m α) := by
  simp only [halaszVinogradovCharacter,Pi.neg_apply,fourier_apply,zsmul_neg,
    AddCircle.toCircle_neg,Circle.coe_inv_eq_conj,map_prod]

lemma halasz_torus_fourier_translation {k : ℕ}
    (g : (Fin k → AddCircle (1:ℝ)) → ℂ) (m : Fin k → ℤ)
    (β : Fin k → AddCircle (1:ℝ)) :
    (∫ α, conj (halaszVinogradovCharacter m α)*g (α+β) ∂halaszVinogradovHaar k) =
      halaszVinogradovCharacter m β*
        ∫ α, conj (halaszVinogradovCharacter m α)*g α ∂halaszVinogradovHaar k := by
  have : (halaszVinogradovHaar k).IsAddRightInvariant := by
    unfold halaszVinogradovHaar
    infer_instance
  rw [← integral_add_right_eq_self
    (fun α => conj (halaszVinogradovCharacter m α)*g (α+β)) (-β)]
  simp only [neg_add_cancel_right,halasz_character_argument_add,
    halasz_character_argument_neg,map_mul,Complex.conj_conj]
  simp_rw [show ∀ α, conj (halaszVinogradovCharacter m α)*
      halaszVinogradovCharacter m β*g α =
      halaszVinogradovCharacter m β*(conj (halaszVinogradovCharacter m α)*g α)
    from fun α => by ring]
  exact integral_const_mul _ _

end TwoPointCorrelations

end OAI
