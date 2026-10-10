import OAI.NumberTheory.JointDickman.Probability.ResidueProductError

namespace OAI

/-! # Product estimates at the opposite endpoint Fourier frequency -/

namespace JointDickman
open Finset

theorem sum_neg_residue_square {q : ℕ} [NeZero q] (F : ZMod q → ℂ) :
    (∑ h : ZMod q, ‖F (-h)‖^2) = ∑ h : ZMod q, ‖F h‖^2 := by
  simpa only [Equiv.neg_apply] using Equiv.sum_comp (Equiv.neg (ZMod q)) (fun h => ‖F h‖^2)

theorem restricted_opposite_residue_product_error_bound {q : ℕ} [NeZero q]
    (P : ZMod q → Prop) [DecidablePred P] (A B C D : ZMod q → ℂ)
    {e₁ e₂ u v : ℝ}
    (h₁ : (∑ r, ‖A r-C r‖^2) ≤ e₁) (h₂ : (∑ r, ‖B r-D r‖^2) ≤ e₂)
    (hC : (∑ r, ‖C r‖^2) ≤ u) (hB : (∑ r, ‖B r‖^2) ≤ v) :
    ‖∑ r, if P r then A r*B (-r)-C r*D (-r) else 0‖ ≤
      Real.sqrt e₁*Real.sqrt v+Real.sqrt u*Real.sqrt e₂ := by
  apply restricted_residue_product_error_bound P A (fun r => B (-r)) C (fun r => D (-r)) h₁
  · change (∑ r, ‖(fun x => B x-D x) (-r)‖^2) ≤ e₂
    rw [sum_neg_residue_square (fun x => B x-D x)]
    exact h₂
  · exact hC
  · simpa only [sum_neg_residue_square] using hB

end JointDickman

end OAI
