import OAI.NumberTheory.Ostmann.Characters.MixedExternalSupportedEnergy
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateLogNorm
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateMaskedSymmetrization
import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkOriginalCoefficient

namespace OAI

/-! # Removing the retained cutoff only from the nonnegative diagonal energy -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingTemplate_log_diagonal_le
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n r m k : ℕ) (hn : n ≤ k)
    (tier : P → ℕ) (outside : List ℕ) (cb cd : ℝ)
    (μ : ℕ → P → ℝ) (hμ : ∀ j a, μ j a ≠ 0 → tier a = j)
    (ν : MovingRegularSlot n r m → P → ℝ) (hν : ∀ j a, 0 ≤ ν j a)
    (hsmall : ∀ y : MovingRegularSlot n r m → P, (∏ j, ν j (y j)) ≠ 0 →
      ∀ j : TreeLeafIndex n × Fin r, tier (y (j.1, .inl j.2)) ≠ k)
    (hbulk : ∀ y : MovingRegularSlot n r m → P, (∏ j, ν j (y j)) ≠ 0 →
      ∀ j : TreeLeafIndex n × Fin m, tier (y (j.1, .inr j.2)) = k)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (G : ℕ → ℝ)
    (active : MovingRegularSlot n r m → Bool) (greg : ∀ q : ℕ, ZMod q → ℂ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v a b center : ℝ) :
    let weighted := fun x s => (movingBulkLeafLogWeight Subtype.val tier k outside cb cd x.data : ℂ) * F x s
    let Cw := fun s y x z => movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V
      weighted φ G n r m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
    let C := fun s y x z => movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V
      F φ G n r m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
    let W := fun s => movingTemplateExternalMultiplier P hP n r m active outside greg s φ Jleft Jright diagonal
    (mixedExternalAverage ν (V n) u v a b center
      (fun s y x z => (‖Cw s y x z‖ ^ 2 : ℂ) * W s y x z)).re ≤
    (mixedExternalAverage ν (V n) u v a b center
      (fun s y x z => (‖C s y x z‖ ^ 2 : ℂ) * W s y x z)).re := by
  intro weighted Cw C W
  have hw (s : ℤ) (y : MovingRegularSlot n r m → P) (x z : ℝ) :
      ((W s y x z).re : ℂ) = W s y x z :=
    (movingTemplateExternalMultiplier_nonneg P hP n r m active outside greg s φ hφ
      Jleft Jright diagonal y x z).2
  have h := mixedExternalAverage_square_mono_support ν hν (V n) u v a b center Cw C
    (fun s y x z => (W s y x z).re)
    (fun s y x z => (movingTemplateExternalMultiplier_nonneg P hP n r m active outside greg s φ hφ
      Jleft Jright diagonal y x z).1)
    (fun y hy s x z => movingTemplateCoefficient_bulk_log_norm_le Subtype.val tier k outside cb cd μ hμ
      childBound pivotBound V F φ G n r m s y hn (hsmall y hy) (hbulk y hy) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)
  simpa only [hw] using h

end Ostmann

end OAI
