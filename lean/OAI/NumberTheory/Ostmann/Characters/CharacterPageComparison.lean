import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterIndexedRealZero
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterRieszLocalDecay

namespace OAI

/-! # Comparing the selected actual Riesz zero with the canonical Page zero -/

namespace Ostmann

open Complex

theorem local_page_fraction (χ : PrimitiveComplexCharacter) (q : ℕ) (T c : ℝ)
    (hq : 1 ≤ q) (hqT : (q : ℝ) ≤ T) (hT : 2 ≤ T)
    (hc : 0 < c) (hcp : c ≤ actualPageConstant / 10) :
    2 * c / (Real.log χ.modulus + Real.log (T + 4) + 1) ≤
      actualPageConstant / Real.log (4 * (q : ℝ)) := by
  let H := Real.log χ.modulus + Real.log (T + 4) + 1
  let L := Real.log (4 * (q : ℝ))
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqp : (0 : ℝ) < q := by linarith
  have hlogq : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
  have hlogT : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hHp : 0 < H := by linarith
  have hLp : 0 < L := Real.log_pos (by linarith)
  have hlog : Real.log (q : ℝ) ≤ Real.log (T + 4) := Real.log_le_log hqp (by linarith)
  have hL : L ≤ 4 * H := by
    have he : L = Real.log 4 + Real.log (q : ℝ) := by
      dsimp [L]
      rw [Real.log_mul (by norm_num) hqp.ne']
    rw [he]
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    dsimp [H] at hH ⊢
    linarith
  change 2 * c / H ≤ actualPageConstant / L
  apply (div_le_div_iff₀ hHp hLp).mpr
  have hm := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 2 * c)
  have hc8 : 8 * c ≤ actualPageConstant := by linarith [actualPageConstant_pos]
  have hh := mul_le_mul_of_nonneg_right hc8 hHp.le
  nlinarith

theorem selected_riesz_zero_canonical (χ : PrimitiveComplexCharacter) (q i : ℕ)
    (T c : ℝ) (hq : 1 ≤ q) (hdvd : χ.modulus ∣ q) (hqT : (q : ℝ) ≤ T)
    (hT : 2 ≤ T) (hc : 0 < c) (hcp : c ≤ actualPageConstant / 10)
    (hsq : χ.character ^ 2 = 1) (him : ((actualCharacterZeros χ).zeros i).im = 0)
    (hbeta : 1 - 2 * c / (Real.log χ.modulus + Real.log (T + 4) + 1) <
      ((actualCharacterZeros χ).zeros i).re) :
    actualLocalZero q = some (indexedRealZero χ i hsq him) := by
  apply indexedRealZero_canonical χ i hsq him q hq hdvd
  have hh := local_page_fraction χ q T c hq hqT hT hc hcp
  linarith

noncomputable def canonicalCharacterRieszTerm (χ : PrimitiveComplexCharacter)
    (q : ℕ) (X : ℝ) : ℂ := by
  classical
  exact match actualLocalZero q with
  | none => 0
  | some e => if e.asRealCharacter.asComplex = χ then
      -rieszContourWeight X (e.beta : ℂ) else 0

theorem selected_riesz_term_eq_canonical (χ : PrimitiveComplexCharacter) (q i : ℕ)
    (T c X : ℝ) (hq : 1 ≤ q) (hdvd : χ.modulus ∣ q) (hqT : (q : ℝ) ≤ T)
    (hT : 2 ≤ T) (hc : 0 < c) (hcp : c ≤ actualPageConstant / 10)
    (hsq : χ.character ^ 2 = 1) (him : ((actualCharacterZeros χ).zeros i).im = 0)
    (hbeta : 1 - 2 * c / (Real.log χ.modulus + Real.log (T + 4) + 1) <
      ((actualCharacterZeros χ).zeros i).re) :
    characterRieszZeroTerm χ X (some i) = canonicalCharacterRieszTerm χ q X := by
  have he := selected_riesz_zero_canonical χ q i T c hq hdvd hqT hT hc hcp hsq him hbeta
  have hz : (((actualCharacterZeros χ).zeros i).re : ℂ) = (actualCharacterZeros χ).zeros i := by
    apply Complex.ext <;> simp [him]
  simp only [canonicalCharacterRieszTerm, he, indexedRealZero_character, ↓reduceIte,
    indexedRealZero_beta, hz, characterRieszZeroTerm]

end Ostmann

end OAI
