import OAI.NumberTheory.Ostmann.ZeroDensity.ActualRealZeroIndices
import OAI.NumberTheory.Ostmann.ZeroDensity.RealCharacterPairZeroBound

namespace OAI

/-! # The real Page exclusion from one-pole bounds -/

namespace Ostmann

open Complex

theorem near_real_zero_inverse_mass (δ β : ℝ) (hδ : 0 < δ) (hβ : β < 1)
    (hnear : 1 - δ / 20 ≤ β) : 9 / 10 < δ * (1 / (1 + δ - β)) := by
  have hh := real_zero_shifted_mass δ (1 + δ - β) hδ (by linarith) (by linarith)
  simp only [div_eq_mul_inv] at hh ⊢
  nlinarith

theorem real_zero_pair_exclusion (e f : PrimitiveRealZero) (δ R S : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : δ * R ≤ 1 / 10) (hS : δ * S ≤ 1 / 10)
    (he : 1 - δ / 20 ≤ e.beta) (hf : 1 - δ / 20 ≤ f.beta)
    (hsingle : shiftedRealCharacterZeroSum e.asRealCharacter ((1 + δ : ℝ) : ℂ) ≤ 1 / δ + R)
    (hpair : e.asRealCharacter ≠ f.asRealCharacter →
      shiftedRealCharacterZeroSum e.asRealCharacter ((1 + δ : ℝ) : ℂ) +
        shiftedRealCharacterZeroSum f.asRealCharacter ((1 + δ : ℝ) : ℂ) ≤ 1 / δ + S) : e = f := by
  have hme := near_real_zero_inverse_mass δ e.beta hδ e.beta_lt_one he
  have hmf := near_real_zero_inverse_mass δ f.beta hδ f.beta_lt_one hf
  have heterm := e.kernel_le_zero_sum (1 + δ) (by linarith) (by linarith)
  have hfterm := f.kernel_le_zero_sum (1 + δ) (by linarith) (by linarith)
  have hcancel (C : ℝ) : δ * (1 / δ + C) = 1 + δ * C := by field_simp
  by_cases hχ : e.asRealCharacter = f.asRealCharacter
  · apply PrimitiveRealZero.eq_of_character_beta hχ
    by_contra hβ
    obtain ⟨i, hi⟩ := e.has_actual_index
    obtain ⟨j, hj⟩ := f.has_actual_index
    rw [← hχ] at hj
    have hij : i ≠ j := by
      intro hij
      apply hβ
      apply Complex.ofReal_injective
      rw [← hi, ← hj, hij]
    have hh := shifted_real_zero_pair_le e.asRealCharacter ((1 + δ : ℝ) : ℂ)
      (by simp; linarith) (by simp; linarith) i j hij
    rw [hi, hj, ← Complex.ofReal_sub, ← Complex.ofReal_sub,
      ← Complex.ofReal_inv, ← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_re] at hh
    have hp := mul_le_mul_of_nonneg_left (hh.trans hsingle) hδ.le
    rw [hcancel] at hp
    simp only [one_div] at hme hmf
    nlinarith
  · have hh := (add_le_add heterm hfterm).trans (hpair hχ)
    have hp := mul_le_mul_of_nonneg_left hh hδ.le
    rw [hcancel] at hp
    nlinarith

end Ostmann

end OAI
