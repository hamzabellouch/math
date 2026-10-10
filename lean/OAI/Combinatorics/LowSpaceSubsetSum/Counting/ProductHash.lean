import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

namespace OAI

/-!
# Independent product-modulus collisions

Sample identities, rather than distinct numerical products, form the finite
probability space. The factors are allowed to repeat. Product divisibility
implies each factor divides the difference, which is all the upper bound needs.
-/

namespace LowSpaceSubsetSum

variable {α β : Type*}

theorem product_divisor_count_le (A : Finset α) (B : Finset β)
    (f : α → ℕ) (g : β → ℕ) (d : ℕ) :
    ((A ×ˢ B).filter fun z => f z.1 * g z.2 ∣ d).card ≤
      (A.filter fun a => f a ∣ d).card * (B.filter fun b => g b ∣ d).card := by
  calc
    _ ≤ ((A.filter fun a => f a ∣ d) ×ˢ (B.filter fun b => g b ∣ d)).card := by
      apply Finset.card_le_card
      intro z hz
      obtain ⟨hzAB, hzd⟩ := Finset.mem_filter.mp hz
      obtain ⟨hza, hzb⟩ := Finset.mem_product.mp hzAB
      apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_filter.mpr ⟨hza, dvd_trans (dvd_mul_right _ _) hzd⟩
      · exact Finset.mem_filter.mpr ⟨hzb, dvd_trans (dvd_mul_left _ _) hzd⟩
    _ = _ := Finset.card_product _ _

/-- Independent uniform sampling multiplies the individual collision bounds.
No coprimality or distinctness of the sampled factors is assumed. -/
theorem product_divisor_probability_le (A : Finset α) (B : Finset β)
    (f : α → ℕ) (g : β → ℕ) (d : ℕ) (hA : A.Nonempty) (hB : B.Nonempty)
    {deltaA deltaB : ℝ} (hdeltaA : 0 ≤ deltaA)
    (ha : ((A.filter fun a => f a ∣ d).card : ℝ) / A.card ≤ deltaA)
    (hb : ((B.filter fun b => g b ∣ d).card : ℝ) / B.card ≤ deltaB) :
    (((A ×ˢ B).filter fun z => f z.1 * g z.2 ∣ d).card : ℝ) /
      (A ×ˢ B).card ≤ deltaA * deltaB := by
  have hA0 : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hB0 : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hcount : (((A ×ˢ B).filter fun z => f z.1 * g z.2 ∣ d).card : ℝ) ≤
      ((A.filter fun a => f a ∣ d).card : ℝ) *
        ((B.filter fun b => g b ∣ d).card : ℝ) := by
    exact_mod_cast product_divisor_count_le A B f g d
  rw [Finset.card_product, Nat.cast_mul]
  calc
    _ ≤ (((A.filter fun a => f a ∣ d).card : ℝ) *
        ((B.filter fun b => g b ∣ d).card : ℝ)) / ((A.card : ℝ) * B.card) :=
      div_le_div_of_nonneg_right hcount (mul_pos hA0 hB0).le
    _ = (((A.filter fun a => f a ∣ d).card : ℝ) / A.card) *
        (((B.filter fun b => g b ∣ d).card : ℝ) / B.card) := by ring
    _ ≤ deltaA * deltaB := mul_le_mul ha hb
      (div_nonneg (Nat.cast_nonneg _) hB0.le) hdeltaA

end LowSpaceSubsetSum

end OAI
