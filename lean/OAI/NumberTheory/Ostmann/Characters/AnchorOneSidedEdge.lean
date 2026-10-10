import OAI.NumberTheory.Ostmann.Characters.AnchorPairCode
import OAI.NumberTheory.Ostmann.ZeroDensity.DirichletGraphFactor

namespace OAI

/-! # A changed anchor code supplies a one-sided squared character -/

namespace Ostmann

theorem changed_anchor_code_one_sided (ε ε' c c' : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hε' : ε' = 1 ∨ ε' = -1)
    (hc : c = 1 ∨ c = -1) (hc' : c' = 1 ∨ c' = -1) (hne : c ≠ c') :
    ((ε * c - ε' * c' = 2 ∨ ε * c - ε' * c' = -2) ∧ ε - ε' = 0) ∨
      (ε * c - ε' * c' = 0 ∧ (ε - ε' = 2 ∨ ε - ε' = -2)) := by
  rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl <;> norm_num at *

theorem signed_square_nonprincipal {p : ℕ} (χ : DirichletCharacter ℂ p)
    (hχ : χ ^ 2 ≠ 1) (e : ℤ) (he : e = 2 ∨ e = -2) : χ ^ e ≠ 1 := by
  rcases he with rfl | rfl
  · simpa only [zpow_ofNat] using hχ
  · intro h
    have hinv := congrArg Inv.inv h
    simp only [zpow_neg, inv_inv, inv_one, zpow_ofNat] at hinv
    exact hχ hinv

/-- The first alternative uses the small anchor as the short modulus; the
second uses the bulk prime as the short modulus and the big anchor as long. -/
theorem changed_anchor_code_characters {p q : ℕ}
    (χanchor : DirichletCharacter ℂ p) (χbulk : DirichletCharacter ℂ q)
    (hanchor : χanchor ^ 2 ≠ 1) (hbulk : χbulk ^ 2 ≠ 1)
    (ε ε' c c' : ℤ) (hε : ε = 1 ∨ ε = -1) (hε' : ε' = 1 ∨ ε' = -1)
    (hc : c = 1 ∨ c = -1) (hc' : c' = 1 ∨ c' = -1) (hne : c ≠ c') :
    (χanchor ^ (ε * c - ε' * c') ≠ 1 ∧ ε - ε' = 0) ∨
      (ε * c - ε' * c' = 0 ∧ χbulk ^ (ε - ε') ≠ 1) := by
  rcases changed_anchor_code_one_sided ε ε' c c' hε hε' hc hc' hne with h | h
  · exact Or.inl ⟨signed_square_nonprincipal χanchor hanchor _ h.1, h.2⟩
  · exact Or.inr ⟨h.1, signed_square_nonprincipal χbulk hbulk _ h.2⟩

end Ostmann

end OAI
