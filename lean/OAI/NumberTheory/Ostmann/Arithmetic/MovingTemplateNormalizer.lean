import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularTemplate
import OAI.NumberTheory.Ostmann.Construction.BadMatchingHarmonicBudget

namespace OAI

/-! # Normalizing the actual regular template, including its small slots -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplate_normalizer_product_le (n r m : ℕ)
    (mass : MovingRegularSlot n r m → ℝ) (L C : ℝ) (hL : 0 < L)
    (hsmall : ∀ j : TreeLeafIndex n × Fin r, Real.exp (-C * L) ≤ mass (j.1, .inl j.2))
    (hbulk : ∀ j : TreeLeafIndex n × Fin m, L ≤ mass (j.1, .inr j.2)) :
    (∏ i, (mass i)⁻¹) ≤
      Real.exp (C * L * (2 ^ n * r : ℕ)) * (L⁻¹) ^ (2 ^ n * m) := by
  have hs (j : TreeLeafIndex n × Fin r) : (mass (j.1, .inl j.2))⁻¹ ≤ Real.exp (C * L) := by
    have h := one_div_le_one_div_of_le (Real.exp_pos (-C * L)) (hsmall j)
    simpa only [one_div, ← Real.exp_neg, neg_mul, neg_neg] using h
  have hb (j : TreeLeafIndex n × Fin m) : (mass (j.1, .inr j.2))⁻¹ ≤ L⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hL (hbulk j)
  have hsp : (∏ j : TreeLeafIndex n × Fin r, (mass (j.1, .inl j.2))⁻¹) ≤
      Real.exp (C * L) ^ (2 ^ n * r) := by
    have h := Finset.prod_le_prod₀
      (fun j (_ : j ∈ (Finset.univ : Finset (TreeLeafIndex n × Fin r))) =>
        inv_nonneg.mpr ((Real.exp_pos _).le.trans (hsmall j))) (fun j _ => hs j)
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_prod,
      card_treeLeafIndex, Fintype.card_fin] using h
  have hbp : (∏ j : TreeLeafIndex n × Fin m, (mass (j.1, .inr j.2))⁻¹) ≤
      (L⁻¹) ^ (2 ^ n * m) := by
    have h := Finset.prod_le_prod₀
      (fun j (_ : j ∈ (Finset.univ : Finset (TreeLeafIndex n × Fin m))) =>
        inv_nonneg.mpr (hL.le.trans (hbulk j))) (fun j _ => hb j)
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_prod,
      card_treeLeafIndex, Fintype.card_fin] using h
  have he : (∏ i, (mass i)⁻¹) =
      (∏ j : TreeLeafIndex n × Fin r, (mass (j.1, .inl j.2))⁻¹) *
        (∏ j : TreeLeafIndex n × Fin m, (mass (j.1, .inr j.2))⁻¹) := by
    simp only [MovingRegularSlot, Fintype.prod_prod_type, Fintype.prod_sum_type,
      Finset.prod_mul_distrib]
  rw [he]
  calc
    _ ≤ Real.exp (C * L) ^ (2 ^ n * r) * (L⁻¹) ^ (2 ^ n * m) :=
      mul_le_mul hsp hbp
        (Finset.prod_nonneg (fun j _ => inv_nonneg.mpr (hL.le.trans (hbulk j))))
        (pow_nonneg (Real.exp_nonneg _) _)
    _ = _ := by rw [← Real.exp_nat_mul]; congr 2; ring

theorem movingTemplate_factorial_normalizer_le (n r m : ℕ)
    (mass : MovingRegularSlot n r m → ℝ) (L C z : ℝ) (hL : 0 < L) (hz : 0 < z)
    (hsize : ((2 ^ n * (r + m) : ℕ) : ℝ) ≤ z * L)
    (hsmall : ∀ j : TreeLeafIndex n × Fin r, Real.exp (-C * L) ≤ mass (j.1, .inl j.2))
    (hbulk : ∀ j : TreeLeafIndex n × Fin m, L ≤ mass (j.1, .inr j.2)) :
    ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) * (∏ i, (mass i)⁻¹) ≤
      Real.exp (Real.log z * (2 ^ n * (r + m) : ℕ) +
        (C * L + Real.log L) * (2 ^ n * r : ℕ)) := by
  have hn := movingTemplate_normalizer_product_le n r m mass L C hL hsmall hbulk
  have hf := factorial_harmonic_entropy 1 (2 ^ n * (r + m)) L z hL hz hsize
  simp only [pow_one, one_mul] at hf
  have hsum : 2 ^ n * (r + m) = 2 ^ n * r + 2 ^ n * m := Nat.mul_add _ _ _
  have hcancel : (L⁻¹) ^ (2 ^ n * r) * L ^ (2 ^ n * r) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hL.ne', one_pow]
  rw [movingRegularSlot_card]
  calc
    _ ≤ ((2 ^ n * (r + m)).factorial : ℝ) *
        (Real.exp (C * L * (2 ^ n * r : ℕ)) * (L⁻¹) ^ (2 ^ n * m)) :=
      mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)
    _ = (((2 ^ n * (r + m)).factorial : ℝ) * (L⁻¹) ^ (2 ^ n * (r + m))) *
        (L ^ (2 ^ n * r) * Real.exp (C * L * (2 ^ n * r : ℕ))) := by
      rw [hsum, pow_add]
      symm
      calc
        _ = (((2 ^ n * r + 2 ^ n * m).factorial : ℝ) *
          (L⁻¹) ^ (2 ^ n * m) * Real.exp (C * L * (2 ^ n * r : ℕ))) *
          ((L⁻¹) ^ (2 ^ n * r) * L ^ (2 ^ n * r)) := by ring
        _ = _ := by rw [hcancel]; ring
    _ ≤ Real.exp (Real.log z * (2 ^ n * (r + m) : ℕ)) *
        (L ^ (2 ^ n * r) * Real.exp (C * L * (2 ^ n * r : ℕ))) :=
      mul_le_mul_of_nonneg_right hf (mul_nonneg (pow_nonneg hL.le _) (Real.exp_nonneg _))
    _ = _ := by
      rw [← Real.exp_log hL, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [Real.log_exp]
      ring

theorem movingTemplate_counterpart_exponential_bound (n r m : ℕ)
    (mass : MovingRegularSlot n r m → ℝ) (L C z cg Gmin cb : ℝ)
    (hL : 0 < L) (hz : 0 < z)
    (hsize : ((2 ^ n * (r + m) : ℕ) : ℝ) ≤ z * L)
    (hsmall : ∀ j : TreeLeafIndex n × Fin r, Real.exp (-C * L) ≤ mass (j.1, .inl j.2))
    (hbulk : ∀ j : TreeLeafIndex n × Fin m, L ≤ mass (j.1, .inr j.2)) :
    Real.exp (cg - Gmin - (2 ^ n : ℕ) * (cb - 1)) *
        ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) * (∏ i, (mass i)⁻¹) ≤
      Real.exp (cg - Gmin - (2 ^ n : ℕ) * (cb - 1) +
        Real.log z * (2 ^ n * (r + m) : ℕ) + (C * L + Real.log L) * (2 ^ n * r : ℕ)) := by
  have h := mul_le_mul_of_nonneg_left
    (movingTemplate_factorial_normalizer_le n r m mass L C z hL hz hsize hsmall hbulk)
    (Real.exp_nonneg (cg - Gmin - (2 ^ n : ℕ) * (cb - 1)))
  rw [← mul_assoc, ← Real.exp_add] at h
  convert h using 1
  congr 1
  ring

end Ostmann

end OAI
