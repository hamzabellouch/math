import OAI.NumberTheory.Ostmann.ZeroDensity.CanonicalRieszKernelBound

namespace OAI

/-! # Replacing the local contour zero by the canonical Page correction -/

namespace Ostmann

open Complex

theorem character_riesz_term_comparison (χ : PrimitiveComplexCharacter) (q : ℕ)
    (T c X C : ℝ) (e : Option ℕ)
    (hq : 1 ≤ q) (hdvd : χ.modulus ∣ q) (hqT : (q : ℝ) ≤ T) (hT : 2 ≤ T)
    (hc : 0 < c) (hcp : c ≤ actualPageConstant / 10) (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hkernel : pageRieszKernelNorm q ≤ C)
    (he : ∀ i, e = some i →
      1 - 2 * c / (Real.log χ.modulus + Real.log (T + 4) + 1) <
        ((actualCharacterZeros χ).zeros i).re ∧
      χ.character ^ 2 = 1 ∧ ((actualCharacterZeros χ).zeros i).im = 0)
    (hec : ∀ i, 1 - c / (Real.log χ.modulus + Real.log (T + 4) + 1) ≤
      ((actualCharacterZeros χ).zeros i).re →
      |((actualCharacterZeros χ).zeros i).im| ≤ T → e = some i) :
    ‖characterRieszZeroTerm χ X e - canonicalCharacterRieszTerm χ q X‖ ≤
      C * X ^ (1 - c / (Real.log χ.modulus + Real.log (T + 4) + 1)) := by
  classical
  have hXp : 0 < X := by linarith
  cases e with
  | some i =>
    obtain ⟨hbeta, hsq, him⟩ := he i rfl
    rw [selected_riesz_term_eq_canonical χ q i T c X hq hdvd hqT hT hc hcp hsq him hbeta,
      sub_self, norm_zero]
    positivity
  | none =>
    simp only [characterRieszZeroTerm, zero_sub, norm_neg]
    cases hpage : actualLocalZero q with
    | none => simp only [canonicalCharacterRieszTerm, hpage, norm_zero]; positivity
    | some r =>
      by_cases hχ : r.asRealCharacter.asComplex = χ
      · have hzero : χ.L (r.beta : ℂ) = 0 := by
          rw [← hχ]
          exact r.zero
        obtain ⟨i, hi⟩ := character_zero_enumerated_of_re_pos χ (r.beta : ℂ)
          (by simpa using r.beta_pos) hzero
        have hβ : r.beta < 1 - c / (Real.log χ.modulus + Real.log (T + 4) + 1) := by
          by_contra hn
          have hh := hec i (by simpa only [hi, Complex.ofReal_re] using not_lt.mp hn)
            (by simp only [hi, Complex.ofReal_im, abs_zero]; linarith)
          cases hh
        have hh := canonicalCharacterRieszTerm_norm_bound χ q X C hXp hC hkernel
        have hp : pageBeta (actualLocalZero q) = r.beta := by simp only [hpage, pageBeta]
        rw [hp] at hh
        exact hh.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hX hβ.le) hC)
      · simp only [canonicalCharacterRieszTerm, hpage, hχ, ↓reduceIte, norm_zero]
        positivity

theorem character_riesz_canonical_bound : ∃ c A B E : ℝ,
    0 < c ∧ c ≤ 1 / 4 ∧ 0 < A ∧ 0 < B ∧ 0 < E ∧
    ∀ (q : ℕ) (χ : PrimitiveComplexCharacter) (T X b : ℝ),
      1 ≤ q → χ.modulus ∣ q → (q : ℝ) ≤ T → 2 ≤ T → 1 ≤ X → 1 < b → b ≤ 2 →
      let H := Real.log χ.modulus + Real.log (T + 4) + 1
      ‖characterRieszMean χ X - canonicalCharacterRieszTerm χ q X‖ ≤
        A * H ^ 2 * X ^ (1 - c / H) + B * H ^ 2 * X ^ b / T ^ 2 +
          2 * (1 / (b - 1) + E) * X ^ b / T := by
  obtain ⟨c, A, B, E, hc, hc4, hcp, hA, hB, hE, hbound⟩ := character_riesz_local_bound
  obtain ⟨C, hC, hkernel⟩ := canonical_riesz_kernel_bound
  refine ⟨c, A + C, B, E, hc, hc4, by positivity, hB, hE, ?_⟩
  intro q χ T X b hq hdvd hqT hT hX hb hb2
  dsimp only
  let H := Real.log χ.modulus + Real.log (T + 4) + 1
  have hqlog : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
  have hTlog : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
  have hH : 1 ≤ H := by dsimp [H]; linarith
  obtain ⟨e, he, hec, hr⟩ := hbound χ T hT
  have hlocal := hr X b hX hb hb2
  have hd := character_riesz_term_comparison χ q T c X C e hq hdvd hqT hT hc hcp hX hC.le
    (hkernel q) he hec
  have ht := norm_sub_le_norm_sub_add_norm_sub (characterRieszMean χ X)
    (characterRieszZeroTerm χ X e) (canonicalCharacterRieszTerm χ q X)
  have hsq : 1 ≤ H ^ 2 := by nlinarith
  have hx : 0 ≤ X ^ (1 - c / H) := Real.rpow_nonneg (by linarith) _
  have hcost : C * X ^ (1 - c / H) ≤ C * H ^ 2 * X ^ (1 - c / H) := by
    have hh := mul_le_mul_of_nonneg_left hsq (mul_nonneg hC.le hx)
    convert hh using 1 <;> ring
  change ‖characterRieszMean χ X - canonicalCharacterRieszTerm χ q X‖ ≤
    (A + C) * H ^ 2 * X ^ (1 - c / H) + B * H ^ 2 * X ^ b / T ^ 2 +
      2 * (1 / (b - 1) + E) * X ^ b / T
  change ‖characterRieszMean χ X - characterRieszZeroTerm χ X e‖ ≤
    A * H ^ 2 * X ^ (1 - c / H) + B * H ^ 2 * X ^ b / T ^ 2 +
      2 * (1 / (b - 1) + E) * X ^ b / T at hlocal
  change ‖characterRieszZeroTerm χ X e - canonicalCharacterRieszTerm χ q X‖ ≤
    C * X ^ (1 - c / H) at hd
  nlinarith

end Ostmann

end OAI
