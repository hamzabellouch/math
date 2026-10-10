import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothPrimePowerRemoval
import OAI.NumberTheory.Ostmann.ZeroDensity.PrimitiveCharacterCard

namespace OAI

/-! # Prime-power removal for a finite primitive character expansion -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def primitiveCharacterPolynomial (F : Finset PrimitiveComplexCharacter)
    (c : PrimitiveComplexCharacter → ℂ) (c₀ : ℂ) (a : ℕ) : ℂ :=
  c₀ + ∑ ρ ∈ F, c ρ * ρ.character (a : ZMod ρ.modulus)

 theorem principal_modulus_one_apply (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
  have hn : IsUnit (n : ZMod 1) := by
    rw [Subsingleton.elim (n : ZMod 1) 1]
    exact isUnit_one
  exact MulChar.one_apply hn

 theorem primitiveCharacterPolynomial_norm (F : Finset PrimitiveComplexCharacter)
    (c : PrimitiveComplexCharacter → ℂ) (c₀ : ℂ) (B : ℝ)
    (hc₀ : ‖c₀‖ ≤ B) (hc : ∀ ρ ∈ F, ‖c ρ‖ ≤ B) (a : ℕ) :
    ‖primitiveCharacterPolynomial F c c₀ a‖ ≤ B * (1 + F.card) := by
  calc
    _ ≤ ‖c₀‖ + ∑ ρ ∈ F, ‖c ρ * ρ.character (a : ZMod ρ.modulus)‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ B + ∑ _ρ ∈ F, B := by
      apply add_le_add hc₀
      apply Finset.sum_le_sum
      intro ρ hρ
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (ρ.character.norm_le_one _)).trans (hc ρ hρ)
    _ = _ := by simp; ring

 theorem character_smooth_mean_identity (F : Finset PrimitiveComplexCharacter)
    (c : PrimitiveComplexCharacter → ℂ) (c₀ : ℂ) (X : ℝ) (hX : 0 < X) :
    c₀ * smoothMangoldtMean 1 1 X +
      ∑ ρ ∈ F, c ρ * smoothMangoldtMean ρ.modulus ρ.character X =
      ∑ a ∈ Finset.Ioc 0 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt a : ℂ) *
        primitiveCharacterPolynomial F c c₀ a * primeMeanTest (a / X) := by
  simp_rw [smoothMangoldtMean_eq_sum _ _ X hX, principal_modulus_one_apply, mul_one]
  unfold primitiveCharacterPolynomial
  simp_rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro a ha
    ring
  · apply Finset.sum_congr rfl
    intro ρ hρ
    apply Finset.sum_congr rfl
    intro a ha
    ring

 theorem character_prime_power_error (F : Finset PrimitiveComplexCharacter)
    (c : PrimitiveComplexCharacter → ℂ) (c₀ : ℂ) (X B : ℝ) (hX : 1 ≤ X)
    (hB : 0 ≤ B) (hc₀ : ‖c₀‖ ≤ B) (hc : ∀ ρ ∈ F, ‖c ρ‖ ≤ B) :
    ‖c₀ * smoothMangoldtMean 1 1 X +
      ∑ ρ ∈ F, c ρ * smoothMangoldtMean ρ.modulus ρ.character X -
      smoothPrimeSum (primitiveCharacterPolynomial F c c₀) X‖ ≤
      (B * (1 + F.card)) * (2 * Real.sqrt X * Real.log X) := by
  rw [character_smooth_mean_identity F c c₀ X (by linarith)]
  exact smooth_mangoldt_prime_error _ X _ hX (by positivity)
    (fun a _ => primitiveCharacterPolynomial_norm F c c₀ B hc₀ hc a)

 theorem character_prime_power_error_of_conductor (F : Finset PrimitiveComplexCharacter)
    (c : PrimitiveComplexCharacter → ℂ) (c₀ : ℂ) (X B : ℝ) (hX : 1 ≤ X)
    (hB : 0 ≤ B) (hc₀ : ‖c₀‖ ≤ B) (hc : ∀ ρ ∈ F, ‖c ρ‖ ≤ B)
    (Q : ℕ) (hQ : ∀ ρ ∈ F, ρ.modulus ≤ Q) :
    ‖c₀ * smoothMangoldtMean 1 1 X +
      ∑ ρ ∈ F, c ρ * smoothMangoldtMean ρ.modulus ρ.character X -
      smoothPrimeSum (primitiveCharacterPolynomial F c c₀) X‖ ≤
      (B * (1 + (Q : ℝ) ^ 2)) * (2 * Real.sqrt X * Real.log X) := by
  apply (character_prime_power_error F c c₀ X B hX hB hc₀ hc).trans
  have hcard : (F.card : ℝ) ≤ (Q : ℝ) ^ 2 := by
    exact_mod_cast primitive_character_family_card F Q hQ
  gcongr
  exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.log_nonneg hX)

end Ostmann

end OAI
