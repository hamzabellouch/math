import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedAverages

namespace OAI

/-! # Concrete norm budgets for the retained arithmetic averages -/

namespace Ostmann
open scoped Classical BigOperators

private theorem finiteMean_norm_le {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℂ) (B : ℝ) (hf : ∀ a, ‖f a‖ ≤ B) :
    ‖(Fintype.card A : ℂ)⁻¹ * ∑ a, f a‖ ≤ B := by
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card A : ℝ)⁻¹ * ∑ _a : A, B :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => hf a))
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

theorem pageGiantWeight_norm_le_two (input : PublishedProgressionInput) (Q q a : ℕ)
    (y : ℝ) (hy : 0 ≤ y) : ‖pageGiantWeight input Q q a y‖ ≤ 2 := by
  have h := pageMultiplier_bounds
    (fun a => pageCoefficient (pageAtModulus q (selectedPageZero input Q)) a)
    (pageBeta (pageAtModulus q (selectedPageZero input Q))) y
    (pageCoefficient_abs_le_one _) (pageBeta_le_one _) hy a
  rw [pageGiantWeight, Complex.norm_real, Real.norm_of_nonneg h.1]
  exact h.2

theorem movingFrequencyPageAverage_norm_le {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ)
    (y : ℝ) (hy : 0 ≤ y) :
    ‖movingFrequencyPageAverage value outside F E T nodes R r input Q y‖ ≤
      2 * (‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) := by
  apply finiteMean_norm_le
  intro z
  have hf : ‖movingFrequencyPairFactor value outside F E T nodes R z.1.val z.2.val.val‖ ≤
      ‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖ := by
    unfold movingFrequencyPairFactor
    split_ifs
    · simp only [norm_mul, Complex.norm_conj, le_refl]
    · exact (norm_zero : ‖(0 : ℂ)‖ = 0) ▸ mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [norm_mul]
  calc
    _ ≤ (‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) * 2 :=
      mul_le_mul hf (pageGiantWeight_norm_le_two input Q r z.2.val.val y hy)
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := mul_comm _ _

theorem movingSpectatorHaarAverage_norm_le {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] (g : ZMod q → ℂ) (D : Bool → (ZMod q)ˣ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (B : ℝ) (hB : 0 ≤ B)
    (hg : ∀ z, ‖g z‖ ≤ B) :
    ‖movingSpectatorHaarAverage value q g D T‖ ≤ B ^ (2 ^ (n + 1)) := by
  apply finiteMean_norm_le
  intro z
  rw [movingSpectatorPairFactor, norm_mul, Complex.norm_conj]
  calc
    _ ≤ B ^ (2 ^ n) * B ^ (2 ^ n) :=
      mul_le_mul (movingModularSpectator_norm value q g (D false) B hB hg (T false) z.1 z.2)
        (movingModularSpectator_norm value q g (D true) B hB hg (T true) z.1 z.2)
        (norm_nonneg _) (pow_nonneg hB _)
    _ = _ := by rw [← pow_add, pow_succ]; congr 1; omega

end Ostmann

end OAI
