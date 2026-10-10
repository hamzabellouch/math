import OAI.NumberTheory.TwoPoint.Basic
import Mathlib.Analysis.Normed.Module.Basic

namespace OAI

/-!
# The endpoint error in the rough-shift averaging argument

These are finite identities and bounds from the proof of (q:rough-shifts)
in quantitative/03-analytic.tex. No short-sum or sieve estimate is assumed.
The averages below use the positive integers `1,...,Y` and translations
`1,...,D`; the resulting error is at most `2D/Y` times the total weight.
-/

namespace TwoPointCorrelations

open scoped BigOperators

/-- A positive prefix, also when its length is zero. -/
def positivePrefix (u : ℕ → ℂ) (Y : ℕ) : ℂ :=
  ∑ v ∈ Finset.range Y, u (v + 1)

/-- The average of the `D` translated positive prefixes. -/
noncomputable def translatedPrefixAverage (u : ℕ → ℂ) (Y D : ℕ) : ℂ :=
  (D : ℂ)⁻¹ * ∑ m ∈ Finset.range D, positivePrefix (fun n => u (n + (m + 1))) Y

theorem positivePrefix_translate_identity (u : ℕ → ℂ) (Y m : ℕ) :
    positivePrefix (fun n => u (n + m)) Y - positivePrefix u Y =
      positivePrefix (fun n => u (n + Y)) m - positivePrefix u m := by
  have hsplit : positivePrefix u Y + positivePrefix (fun n => u (n + Y)) m =
      positivePrefix u m + positivePrefix (fun n => u (n + m)) Y := by
    have h₁ : positivePrefix u (Y + m) =
        positivePrefix u Y + positivePrefix (fun n => u (n + Y)) m := by
      simpa only [positivePrefix, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        Finset.sum_range_add (fun n => u (n + 1)) Y m
    have h₂ : positivePrefix u (m + Y) =
        positivePrefix u m + positivePrefix (fun n => u (n + m)) Y := by
      simpa only [positivePrefix, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        Finset.sum_range_add (fun n => u (n + 1)) m Y
    exact h₁.symm.trans ((congrArg (positivePrefix u) (Nat.add_comm Y m)).trans h₂)
  linear_combination -hsplit

theorem norm_positivePrefix_le (u : ℕ → ℂ) (Y : ℕ) (B : ℝ)
    (hu : ∀ n, 0 < n → ‖u n‖ ≤ B) : ‖positivePrefix u Y‖ ≤ Y * B := by
  calc
    _ ≤ ∑ v ∈ Finset.range Y, ‖u (v + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ Finset.range Y, B :=
      Finset.sum_le_sum (fun v _ => hu (v + 1) (by omega))
    _ = _ := by simp

/-- Translating by `m` loses at most `m` terms at each endpoint. No relation
between the prefix length and the translation is needed. -/
theorem norm_positivePrefix_translate_sub_le (u : ℕ → ℂ) (Y m : ℕ) (B : ℝ)
    (hu : ∀ n, 0 < n → ‖u n‖ ≤ B) :
    ‖positivePrefix (fun n => u (n + m)) Y - positivePrefix u Y‖ ≤ 2 * m * B := by
  rw [positivePrefix_translate_identity]
  calc
    _ ≤ ‖positivePrefix (fun n => u (n + Y)) m‖ + ‖positivePrefix u m‖ :=
      norm_sub_le _ _
    _ ≤ (m : ℝ) * B + m * B := add_le_add
      (norm_positivePrefix_le _ _ _ (fun n hn => hu _ (by omega)))
      (norm_positivePrefix_le _ _ _ hu)
    _ = _ := by ring

/-- Averaging positive translations has the same finite endpoint bound. -/
theorem norm_translatedPrefixAverage_sub_le (u : ℕ → ℂ) (Y D : ℕ)
    (hD : 0 < D) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ n, 0 < n → ‖u n‖ ≤ B) :
    ‖translatedPrefixAverage u Y D - positivePrefix u Y‖ ≤ 2 * D * B := by
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have heq : translatedPrefixAverage u Y D - positivePrefix u Y =
      (D : ℂ)⁻¹ * ∑ m ∈ Finset.range D,
        (positivePrefix (fun n => u (n + (m + 1))) Y - positivePrefix u Y) := by
    simp only [translatedPrefixAverage, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_sub]
    field_simp
  rw [heq, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (D : ℝ)⁻¹ * ∑ m ∈ Finset.range D,
        ‖positivePrefix (fun n => u (n + (m + 1))) Y - positivePrefix u Y‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hDr.le)
    _ ≤ (D : ℝ)⁻¹ * ∑ _m ∈ Finset.range D, (2 * D * B) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hDr.le)
      apply Finset.sum_le_sum
      intro m hm
      apply (norm_positivePrefix_translate_sub_le u Y (m + 1) B hu).trans
      have hmD : ((m + 1 : ℕ) : ℝ) ≤ D := by
        exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hm))
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmD (by norm_num : (0 : ℝ) ≤ 2)) hB
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp

/-- The normalized endpoint error, in exactly the `D/Y` scale used in
the rough-shift lemma. -/
theorem norm_normalized_translation_error (u : ℕ → ℂ) (Y D : ℕ)
    (hY : 0 < Y) (hD : 0 < D) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ n, 0 < n → ‖u n‖ ≤ B) :
    ‖(translatedPrefixAverage u Y D - positivePrefix u Y) / (Y : ℂ)‖ ≤
      2 * (D : ℝ) / Y * B := by
  rw [norm_div, Complex.norm_natCast]
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  apply (div_le_div_of_nonneg_right
    (norm_translatedPrefixAverage_sub_le u Y D hD B hB hu) hYr.le).trans
  exact le_of_eq (by ring)

/-- The actual weighted progression-correlation profile. -/
def weightedShiftProfile {ι : Type*} (Z : Finset ι) (w : ι → ℂ) (shift : ι → ℕ)
    (f g : ℕ → ℂ) (l b n : ℕ) : ℂ :=
  ∑ z ∈ Z, w z * (if n % l = b % l then f n * g (n + shift z) else 0)

theorem norm_weightedShiftProfile_le {ι : Type*} (Z : Finset ι) (w : ι → ℂ)
    (shift : ι → ℕ) (f g : ℕ → ℂ) (hf : OneBounded f) (hg : OneBounded g)
    (l b n : ℕ) (hn : 0 < n) :
    ‖weightedShiftProfile Z w shift f g l b n‖ ≤ ∑ z ∈ Z, ‖w z‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro z _
  by_cases hmod : n % l = b % l
  · simp only [hmod, ite_true, norm_mul]
    have hprod := mul_le_mul (hf n hn) (hg _ (by omega))
      (norm_nonneg (g (n + shift z))) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod (norm_nonneg (w z))
  · simp only [hmod, ite_false, mul_zero, norm_zero]
    exact norm_nonneg _

theorem weighted_rough_shift_boundary {ι : Type*} (Z : Finset ι) (w : ι → ℂ)
    (shift : ι → ℕ) (f g : ℕ → ℂ) (hf : OneBounded f) (hg : OneBounded g)
    (l b Y D : ℕ) (hY : 0 < Y) (hD : 0 < D) :
    ‖(translatedPrefixAverage (weightedShiftProfile Z w shift f g l b) Y D -
        positivePrefix (weightedShiftProfile Z w shift f g l b) Y) / (Y : ℂ)‖ ≤
      2 * (D : ℝ) / Y * ∑ z ∈ Z, ‖w z‖ := by
  exact norm_normalized_translation_error _ Y D hY hD _
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (fun n hn => norm_weightedShiftProfile_le Z w shift f g hf hg l b n hn)

end TwoPointCorrelations

end OAI
