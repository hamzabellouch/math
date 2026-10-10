import OAI.NumberTheory.TwoPoint.Bounds.ResidueExpansion
import OAI.NumberTheory.TwoPoint.Bounds.ShortSumSampling
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace OAI

/-! Finite multiplicative Fourier inversion on the unit residues. The
L1 coefficient bound follows from Parseval and Cauchy--Schwarz and requires
no primitive-character or Gauss-sum estimate. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical ComplexConjugate

noncomputable def mrtCharacterFourierCoefficient {q : ℕ} [NeZero q]
    (A : ZMod q → ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ b : ZMod q, A b * conj (χ b)

lemma mrt_character_fourier_kernel {q : ℕ} [NeZero q] (b z : ZMod q) :
    (∑ χ : DirichletCharacter ℂ q, conj (χ b) * χ z) =
      if b = z then if IsUnit z then (q.totient : ℂ) else 0 else 0 := by
  by_cases hb : IsUnit b
  · simp_rw [character_conj_unit _ hb]
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb z]
    by_cases he : b = z
    · subst z
      simp [hb]
    · simp [he]
  · have hz (χ : DirichletCharacter ℂ q) : χ b = 0 := χ.map_nonunit hb
    simp only [hz, map_zero, zero_mul, sum_const_zero]
    by_cases he : b = z
    · subst z
      simp [hb]
    · simp [he]

theorem mrt_character_fourier_inversion {q : ℕ} [NeZero q]
    (A : ZMod q → ℂ) (z : ZMod q) :
    (∑ χ : DirichletCharacter ℂ q, mrtCharacterFourierCoefficient A χ * χ z) =
      if IsUnit z then A z else 0 := by
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have he (χ : DirichletCharacter ℂ q) : mrtCharacterFourierCoefficient A χ * χ z =
      (q.totient : ℂ)⁻¹ * ∑ b : ZMod q, A b * (conj (χ b) * χ z) := by
    unfold mrtCharacterFourierCoefficient
    rw [mul_assoc, sum_mul]
    congr 1
    apply sum_congr rfl
    intro b _
    ring
  calc
    _ = (q.totient : ℂ)⁻¹ * ∑ b : ZMod q, A b *
        ∑ χ : DirichletCharacter ℂ q, conj (χ b) * χ z := by
      simp_rw [he]
      rw [← mul_sum, sum_comm]
      simp only [mul_sum]
    _ = (q.totient : ℂ)⁻¹ *
        (A z * (if IsUnit z then (q.totient : ℂ) else 0)) := by
      simp only [mrt_character_fourier_kernel, mul_ite, mul_zero]
      rw [sum_eq_single z]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    _ = _ := by
      by_cases hz : IsUnit z <;> simp [hz, hφ, mul_comm]

lemma mrt_character_coefficient_conj {q : ℕ} [NeZero q]
    (A : ZMod q → ℂ) (χ : DirichletCharacter ℂ q) :
    conj (mrtCharacterFourierCoefficient A χ) =
      (q.totient : ℂ)⁻¹ * ∑ b : ZMod q, conj (A b) * χ b := by
  simp only [mrtCharacterFourierCoefficient, map_mul, map_inv₀, map_sum,
    map_natCast, Complex.conj_conj]

theorem mrt_character_fourier_parseval {q : ℕ} [NeZero q] (A : ZMod q → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖mrtCharacterFourierCoefficient A χ‖ ^ 2) =
      (q.totient : ℝ)⁻¹ * ∑ b : ZMod q, if IsUnit b then ‖A b‖ ^ 2 else 0 := by
  have he (χ : DirichletCharacter ℂ q) :
      mrtCharacterFourierCoefficient A χ * conj (mrtCharacterFourierCoefficient A χ) =
      (q.totient : ℂ)⁻¹ * ∑ b : ZMod q,
        conj (A b) * (mrtCharacterFourierCoefficient A χ * χ b) := by
    rw [mrt_character_coefficient_conj]
    calc
      _ = (q.totient : ℂ)⁻¹ *
          (mrtCharacterFourierCoefficient A χ * ∑ b : ZMod q, conj (A b) * χ b) := by ring
      _ = _ := by
        rw [mul_sum]
        congr 1
        apply sum_congr rfl
        intro b _
        ring
  apply Complex.ofReal_injective
  push_cast
  calc
    _ = ∑ χ : DirichletCharacter ℂ q,
        mrtCharacterFourierCoefficient A χ * conj (mrtCharacterFourierCoefficient A χ) := by
      apply sum_congr rfl
      intro χ _
      exact (Complex.mul_conj' _).symm
    _ = (q.totient : ℂ)⁻¹ * ∑ b : ZMod q, conj (A b) *
        ∑ χ : DirichletCharacter ℂ q, mrtCharacterFourierCoefficient A χ * χ b := by
      simp_rw [he]
      rw [← mul_sum, sum_comm]
      simp only [mul_sum]
    _ = (q.totient : ℂ)⁻¹ * ∑ b : ZMod q,
        conj (A b) * (if IsUnit b then A b else 0) := by
      simp only [mrt_character_fourier_inversion]
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro b _
      by_cases hb : IsUnit b
      · simpa only [hb, ite_true, Complex.ofReal_pow] using Complex.conj_mul' (A b)
      · simp [hb]

theorem mrt_character_fourier_l1 {q : ℕ} [NeZero q] (A : ZMod q → ℂ)
    (hA : ∀ b, ‖A b‖ ≤ 1) :
    (∑ χ : DirichletCharacter ℂ q, ‖mrtCharacterFourierCoefficient A χ‖) ≤
      Real.sqrt (q : ℝ) := by
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  have hc := sum_mul_sq_le_sq_mul_sq (univ : Finset (DirichletCharacter ℂ q))
    (fun _ => (1 : ℝ)) (fun χ => ‖mrtCharacterFourierCoefficient A χ‖)
  simp only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one, hcard] at hc
  rw [mrt_character_fourier_parseval, ← mul_assoc, mul_inv_cancel₀ hφ.ne', one_mul] at hc
  have hm : (∑ b : ZMod q, if IsUnit b then ‖A b‖ ^ 2 else 0) ≤ (q : ℝ) := by
    calc
      _ ≤ ∑ _b : ZMod q, (1 : ℝ) := by
        apply sum_le_sum
        intro b _
        by_cases hb : IsUnit b
        · simp only [hb, ite_true]
          nlinarith [norm_nonneg (A b), hA b]
        · simp [hb]
      _ = _ := by simp [ZMod.card]
  have hs := hc.trans hm
  have hn : 0 ≤ ∑ χ : DirichletCharacter ℂ q, ‖mrtCharacterFourierCoefficient A χ‖ :=
    sum_nonneg (fun _ _ => norm_nonneg _)
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg q), Real.sqrt_nonneg (q : ℝ)]

noncomputable def mrtAdditiveCharacterCoefficient (q : ℕ) [NeZero q] (r : ℤ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  mrtCharacterFourierCoefficient (fun b : ZMod q => additiveCharacter ((r : ℝ) / q) b.val) χ

theorem mrt_additive_character_inversion (q : ℕ) [NeZero q] (r : ℤ) (z : ZMod q) :
    (∑ χ : DirichletCharacter ℂ q, mrtAdditiveCharacterCoefficient q r χ * χ z) =
      if IsUnit z then additiveCharacter ((r : ℝ) / q) z.val else 0 :=
  mrt_character_fourier_inversion _ z

theorem mrt_additive_character_l1 (q : ℕ) [NeZero q] (r : ℤ) :
    (∑ χ : DirichletCharacter ℂ q, ‖mrtAdditiveCharacterCoefficient q r χ‖) ≤
      Real.sqrt (q : ℝ) := by
  apply mrt_character_fourier_l1
  intro b
  exact (norm_additiveCharacter _ _).le

end TwoPointCorrelations

end OAI
