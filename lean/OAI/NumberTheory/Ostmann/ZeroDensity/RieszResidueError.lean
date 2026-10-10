import OAI.NumberTheory.Ostmann.ZeroDensity.InducedCharacterRieszDecay

namespace OAI

/-! # Passing uniform character errors to a single residue class -/

namespace Ostmann

open Complex Filter
open scoped BigOperators

theorem rieszResidueMean_error_bound (q : ℕ) [NeZero q] (a : ZMod q)
    (ha : IsUnit a) (X E : ℝ) (_hE : 0 ≤ E) (M : DirichletCharacter ℂ q → ℂ)
    (herror : ∀ χ, ‖rieszTwistMean (fun n => χ (n : ZMod q)) X - M χ‖ ≤ E) :
    ‖(q.totient : ℂ) * rieszResidueMean q a X - ∑ χ, χ a⁻¹ * M χ‖ ≤ (q.totient : ℝ) * E := by
  rw [rieszResidueMean_orthogonality q a ha X, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ χ : DirichletCharacter ℂ q,
        ‖χ a⁻¹ * rieszTwistMean (fun n => χ (n : ZMod q)) X - χ a⁻¹ * M χ‖ := norm_sum_le _ _
    _ ≤ ∑ _χ : DirichletCharacter ℂ q, E := by
      apply Finset.sum_le_sum
      intro χ _
      rw [← mul_sub, norm_mul]
      exact (mul_le_mul (χ.norm_le_one _) (herror χ) (norm_nonneg _) zero_le_one).trans_eq (one_mul E)
    _ = (q.totient : ℝ) * E := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]

theorem rieszResidueMean_average_error_bound (q : ℕ) [NeZero q] (a : ZMod q)
    (ha : IsUnit a) (X E : ℝ) (hE : 0 ≤ E) (M : DirichletCharacter ℂ q → ℂ)
    (herror : ∀ χ, ‖rieszTwistMean (fun n => χ (n : ZMod q)) X - M χ‖ ≤ E) :
    ‖rieszResidueMean q a X - (q.totient : ℂ)⁻¹ * ∑ χ, χ a⁻¹ * M χ‖ ≤ E := by
  have ht := rieszResidueMean_error_bound q a ha X E hE M herror
  have hpos : 0 < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hne : (q.totient : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have heq : (q.totient : ℂ) * (rieszResidueMean q a X -
      (q.totient : ℂ)⁻¹ * ∑ χ, χ a⁻¹ * M χ) =
      (q.totient : ℂ) * rieszResidueMean q a X - ∑ χ, χ a⁻¹ * M χ := by
    field_simp
  rw [← heq, norm_mul, Complex.norm_natCast] at ht
  exact (mul_le_mul_iff_right₀ hpos).mp (by simpa only [mul_comm] using ht)

theorem rieszResidueMean_reduced_error : ∃ d : ℝ, 0 < d ∧
    ∀ᶠ X : ℝ in atTop, ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.exp (Real.sqrt (Real.log X)) →
      ∀ [NeZero q] (a : ZMod q), IsUnit a →
        ‖rieszResidueMean q a X - (q.totient : ℂ)⁻¹ *
            ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ *
              reducedRieszMain q (primitiveCharacterReduction χ) X‖ ≤
          4 * X * Real.exp (-d * Real.sqrt (Real.log X)) := by
  obtain ⟨d, hd, h⟩ := induced_character_riesz_decay
  refine ⟨d, hd, ?_⟩
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with X hX hX1
  intro q hq hqX inst a ha
  exact rieszResidueMean_average_error_bound q a ha X _ (by positivity) _ (hX q hq hqX)

end Ostmann

end OAI
