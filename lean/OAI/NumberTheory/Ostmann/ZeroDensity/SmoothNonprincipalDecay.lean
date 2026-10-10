import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothFamilyEnvelopes
import OAI.NumberTheory.Ostmann.Construction.SmoothMeanDecayRates
import OAI.NumberTheory.Ostmann.ZeroDensity.RetainedLowZeroDecay

namespace OAI

/-! # The nonprincipal part of manuscript Lemma 5.3

This is derived from the three precisely recorded analytic inputs.  The
exception is one entire primitive character, uniformly for every finite family.
-/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem smooth_nonprincipal_decay (Z : ∀ χ, ComplexZeroEnumeration χ)
    (hD : PublishedComplexZeroDensity Z) (hR : PublishedComplexZeroRegion Z)
    (P : PublishedSmoothExplicitFormula Z) (a D : ℝ) (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 101 ≤ Q →
      L ^ 2 ≤ Real.log Q → Real.log Q ≤ a * L * Real.exp ((9 / 10 : ℝ) * L) →
      ∃ exception : Option PrimitiveComplexCharacter,
      ∀ F : Finset PrimitiveComplexCharacter,
        (∀ χ ∈ F, χ.modulus ≤ Q) → (∀ χ ∈ F, some χ ≠ exception) →
        (∑ χ ∈ F, ‖smoothMangoldtMean χ.modulus χ.character (Real.exp (Real.exp L))‖) ≤
          Real.exp (Real.exp L) * Real.exp (-D * L) := by
  have hm := P.mellinConstant_pos.le
  have hz := P.zeroCountConstant_pos.le
  have he := P.errorConstant_pos.le
  filter_upwards [retained_low_zero_decay Z hD hR a (D + 1) ha,
    eventual_conductor_exponential_decay a 8 (16 * P.mellinConstant * P.zeroCountConstant)
      (D + 1) ha (by norm_num),
    eventual_conductor_negative_decay (128 * P.mellinConstant * P.zeroCountConstant ^ 2) (D + 1),
    eventual_conductor_exponential_decay a 3 (P.mellinConstant + 2 * P.errorConstant)
      (D + 1) ha (by norm_num),
    Real.tendsto_exp_atTop.eventually_ge_atTop (P.mellinConstant + 3),
    eventually_ge_atTop (1 : ℝ)] with L hlow hmid hhigh hrem hcoef hL
  intro Q hQ hQL hQU
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hq : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hX1 : 1 ≤ Real.exp (Real.exp L) := Real.one_le_exp (Real.exp_nonneg _)
  have hX2 : 2 ≤ Real.exp (Real.exp L) := by
    have hh := Real.add_one_le_exp (Real.exp L)
    have hh' : 1 ≤ Real.exp L := Real.one_le_exp (by linarith)
    linarith
  obtain ⟨exception, hlow⟩ := hlow Q hQ hQU
  refine ⟨exception, ?_⟩
  intro F hF hFE
  have hmain := smooth_nonprincipal_family_bound P Q (by omega) F hF
    ((Q : ℝ) ^ 5) (Real.exp (Real.exp L)) (by positivity) hX2
  have hl := hlow F hF hFE
  have hl' := mul_le_mul_of_nonneg_left hl
    (mul_nonneg (Real.exp_nonneg (Real.exp L)) hm)
  have hmid0 := smooth_middle_zero_envelope P.mellinConstant P.zeroCountConstant
    (Q : ℝ) (Real.exp (Real.exp L)) hm hz hQ1 (Real.exp_pos _)
  have hhigh0 := smooth_high_zero_envelope P.mellinConstant P.zeroCountConstant
    (Q : ℝ) (Real.exp (Real.exp L)) hm hz hQ1 (Real.exp_nonneg _)
  have hrem0 := smooth_family_remainder_envelope P.mellinConstant P.errorConstant
    (Q : ℝ) (Real.exp (Real.exp L)) F.card hm he hQ1 hX1
    (by exact_mod_cast primitive_character_family_card F Q hF)
  simp only [Real.log_exp] at hmain hmid0 hrem0
  have hmid1 := mul_le_mul_of_nonneg_left (hmid (Real.log Q) hq hQU)
    (Real.exp_nonneg (Real.exp L))
  have hhigh1 := mul_le_mul_of_nonneg_left (hhigh (Real.log Q) hQL)
    (Real.exp_nonneg (Real.exp L))
  have hrem1 := mul_le_mul_of_nonneg_left (hrem (Real.log Q) hq hQU)
    (Real.exp_nonneg (Real.exp L))
  have hsum : (∑ χ ∈ F, ‖smoothMangoldtMean χ.modulus χ.character
      (Real.exp (Real.exp L))‖) ≤ Real.exp (Real.exp L) *
        ((P.mellinConstant + 3) * Real.exp (-(D + 1) * L)) := by
    nlinarith [hmain, hl', hmid0, hmid1, hhigh0, hhigh1, hrem0, hrem1]
  apply hsum.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  calc
    _ ≤ Real.exp L * Real.exp (-(D + 1) * L) :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
