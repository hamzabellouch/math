import OAI.NumberTheory.Ostmann.Characters.CharacterFourthMoment

namespace OAI

/-!
# The weighted character fourth-moment bound

Equation `tree-fourth-moment` follows from character orthogonality and
counting coincidences of two monic split quadratics.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance characterFourthBoundFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

/-- The fourth-moment bound, with the manuscript's normalization. -/
theorem weightedCharacterSum_fourth_bound {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ b, 0 ≤ w b) :
    (∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, ‖weightedCharacterSum w χ a‖ ^ 4) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤
        2 * (p : ℝ) * (∑ b : ZMod p, w b ^ 2) ^ 2 + (∑ b : ZMod p, w b) ^ 4 := by
  classical
  let W : ZMod p → ZMod p → ZMod p → ZMod p → ℝ :=
    fun b₁ b₂ b₃ b₄ => w b₁ * w b₂ * w b₃ * w b₄
  let V : ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ℝ :=
    fun a b₁ b₂ b₃ b₄ =>
      if (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄) ∧
          (a - b₁) * (a - b₂) ≠ 0 then W b₁ b₂ b₃ b₄ else 0
  have hW (b₁ b₂ b₃ b₄ : ZMod p) : 0 ≤ W b₁ b₂ b₃ b₄ :=
    mul_nonneg (mul_nonneg (mul_nonneg (hw _) (hw _)) (hw _)) (hw _)
  have hswap : (∑ a : ZMod p, ∑ b₁ : ZMod p, ∑ b₂ : ZMod p,
      ∑ b₃ : ZMod p, ∑ b₄ : ZMod p, V a b₁ b₂ b₃ b₄) =
      ∑ b₁ : ZMod p, ∑ b₂ : ZMod p, ∑ b₃ : ZMod p,
        ∑ b₄ : ZMod p, ∑ a : ZMod p, V a b₁ b₂ b₃ b₄ := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b₁ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b₂ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b₃ _
    rw [Finset.sum_comm]
  have hlocal (b₁ b₂ b₃ b₄ : ZMod p) : (∑ a : ZMod p, V a b₁ b₂ b₃ b₄) ≤
      W b₁ b₂ b₃ b₄ *
        ((Finset.univ.filter (fun a : ZMod p =>
          (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄))).card : ℝ) := by
    calc
      _ ≤ ∑ a : ZMod p,
          if (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄) then W b₁ b₂ b₃ b₄ else 0 := by
        apply Finset.sum_le_sum
        intro a _
        dsimp only [V]
        by_cases he : (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄)
        · rw [ite_eq_left he]
          by_cases hn : (a - b₁) * (a - b₂) ≠ 0
          · rw [ite_eq_left ⟨he, hn⟩]
          · rw [ite_eq_right (fun h => hn h.2)]
            exact hW b₁ b₂ b₃ b₄
        · rw [ite_eq_right he, ite_eq_right (fun h => he h.1)]
      _ = _ := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  have hsum : (∑ a : ZMod p, ∑ b₁ : ZMod p, ∑ b₂ : ZMod p,
      ∑ b₃ : ZMod p, ∑ b₄ : ZMod p, V a b₁ b₂ b₃ b₄) ≤
      2 * (p : ℝ) * (∑ b : ZMod p, w b ^ 2) ^ 2 + (∑ b : ZMod p, w b) ^ 4 := by
    rw [hswap]
    calc
      _ ≤ ∑ b₁ : ZMod p, ∑ b₂ : ZMod p, ∑ b₃ : ZMod p, ∑ b₄ : ZMod p,
          W b₁ b₂ b₃ b₄ *
            ((Finset.univ.filter (fun a : ZMod p =>
              (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄))).card : ℝ) := by
        exact Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ =>
          Finset.sum_le_sum fun b₃ _ => Finset.sum_le_sum fun b₄ _ => hlocal b₁ b₂ b₃ b₄
      _ ≤ _ := by simpa only [W, ZMod.card] using weighted_quadratic_collisions_le w hw
  have hcard : 0 < (Fintype.card (ZMod p)ˣ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hcard).mpr
  rw [Finset.sum_comm]
  simp_rw [weightedCharacterSum_fourth_character_sum]
  rw [← Finset.mul_sum]
  simpa only [V, W, mul_comm] using mul_le_mul_of_nonneg_left hsum hcard.le

end Ostmann

end OAI
