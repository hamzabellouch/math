import OAI.NumberTheory.Ostmann.Characters.ProductWeightVariation

namespace OAI

/-! # The original reciprocal-integer weight in partial summation -/

namespace Ostmann

open scoped BigOperators

theorem discreteVariation_nonneg (f : ℕ → ℂ) (N : ℕ) : 0 ≤ discreteVariation f N := by
  exact add_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

theorem discreteVariation_congr {f g : ℕ → ℂ} {N : ℕ}
    (h : ∀ j ≤ N - 1, f j = g j) : discreteVariation f N = discreteVariation g N := by
  unfold discreteVariation
  rw [h (N - 1) le_rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [h j (by omega), h (j + 1) (by omega)]

theorem discreteVariation_ofReal_antitone (u : ℕ → ℝ) (N : ℕ)
    (hu : ∀ j, 0 ≤ u j) (hanti : Antitone u) :
    discreteVariation (fun j => (u j : ℂ)) N = u 0 := by
  have hs (j : ℕ) : ‖(u (j + 1) : ℂ) - (u j : ℂ)‖ = u j - u (j + 1) := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (hanti (by omega)))]
    ring
  unfold discreteVariation
  simp only [Complex.norm_real, Real.norm_of_nonneg (hu _), hs]
  rw [Finset.sum_range_sub']
  ring

theorem reciprocal_progression_antitone (b d : ℝ) (hb : 0 < b) (hd : 0 ≤ d) :
    Antitone (fun j : ℕ => (b + d * j)⁻¹) := by
  intro i j hij
  have hi : 0 < b + d * i := lt_of_lt_of_le hb (le_add_of_nonneg_right (mul_nonneg hd (Nat.cast_nonneg _)))
  have hijR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  have hj : b + d * i ≤ b + d * j :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_left hijR hd)
  exact inv_anti₀ hi hj

theorem reciprocal_progression_variation (b d : ℝ) (hb : 0 < b) (hd : 0 ≤ d) (N : ℕ) :
    discreteVariation (fun j => Complex.ofReal ((b + d * (j : ℝ))⁻¹)) N = b⁻¹ := by
  simpa using discreteVariation_ofReal_antitone (fun j => (b + d * j)⁻¹) N
    (fun j => inv_nonneg.mpr (by positivity)) (reciprocal_progression_antitone b d hb hd)

theorem reciprocal_progression_norm (b d : ℝ) (hb : 0 < b) (hd : 0 ≤ d) (j : ℕ) :
    ‖Complex.ofReal ((b + d * (j : ℝ))⁻¹)‖ ≤ b⁻¹ := by
  rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
  simpa using reciprocal_progression_antitone b d hb hd (Nat.zero_le j)

/-- Multiplying by 1/n costs only twice the endpoint bound divided by the
left endpoint, with no dependence on the progression length. -/
theorem reciprocal_progression_product_variation (b d : ℝ) (hb : 0 < b) (hd : 0 ≤ d)
    (f : ℕ → ℂ) (N : ℕ) (B V : ℝ) (hBV : B ≤ V)
    (hf : ∀ j, ‖f j‖ ≤ B) (hv : discreteVariation f N ≤ V) :
    discreteVariation (fun j => Complex.ofReal ((b + d * (j : ℝ))⁻¹) * f j) N ≤ 2 * b⁻¹ * V := by
  have hB : 0 ≤ B := (norm_nonneg (f 0)).trans (hf 0)
  have ht := discreteVariation_mul (fun j => Complex.ofReal ((b + d * (j : ℝ))⁻¹)) f b⁻¹ B N hB
    (reciprocal_progression_norm b d hb hd) hf
  rw [reciprocal_progression_variation b d hb hd] at ht
  apply ht.trans
  nlinarith [mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hb.le),
    mul_le_mul_of_nonneg_right hBV (inv_nonneg.mpr hb.le)]

theorem discreteVariation_const_mul (c : ℂ) (f : ℕ → ℂ) (N : ℕ) :
    discreteVariation (fun j => c * f j) N = ‖c‖ * discreteVariation f N := by
  simp only [discreteVariation, ← mul_sub, norm_mul, Finset.mul_sum, mul_add]

end Ostmann

end OAI
