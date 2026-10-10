import OAI.NumberTheory.TwoPoint.Bounds.ReciprocalPaddingLaw
import OAI.NumberTheory.TwoPoint.Bounds.PaddingLogMoment

namespace OAI

/-! Under the exact harmonic padding law, more than half the mass obeys
both the degree and logarithmic-size restrictions used to form the bins. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma FiniteLaw.probability_lt_le_average {A : Type*} [Fintype A]
    (μ : FiniteLaw A) (Z : A → ℝ) (hZ : ∀ x, 0 ≤ Z x) (t : ℝ) (ht : 0 < t) :
    μ.probability (fun x => t < Z x) ≤ μ.average Z / t := by
  calc
    _ ≤ μ.average (fun x => Z x / t) := by
      apply μ.average_mono
      intro x
      by_cases hx : t < Z x
      · rw [ite_eq_left hx]
        exact (one_le_div ht).mpr hx.le
      · rw [ite_eq_right hx]
        exact div_nonneg (hZ x) ht.le
    _ = _ := by
      simp only [div_eq_mul_inv, μ.average_mul_const]

lemma FiniteLaw.probability_and_ge {A : Type*} [Fintype A]
    (μ : FiniteLaw A) (E F : A → Prop) :
    1 - μ.probability (fun x => ¬ E x) - μ.probability (fun x => ¬ F x) ≤
      μ.probability (fun x => E x ∧ F x) := by
  have hh := μ.average_mono (f := fun x =>
    1 - (if ¬ E x then 1 else 0) - (if ¬ F x then 1 else 0))
    (g := fun x => if E x ∧ F x then 1 else 0) (fun x => by
      by_cases he : E x <;> by_cases hf : F x <;> simp [he, hf])
  simpa [FiniteLaw.average, FiniteLaw.probability, mul_sub,
    sum_sub_distrib, μ.total] using hh

lemma booleanCount_nonneg {ι : Type*} [Fintype ι] (a : ι → Bool) : 0 ≤ booleanCount a := by
  apply sum_nonneg
  intro i _
  split_ifs <;> norm_num

lemma paddingLog_nonneg (Q : Finset ℕ) (b : Q → Bool) : 0 ≤ paddingLog Q b := by
  apply sum_nonneg
  intro p _
  split_ifs
  · exact log_nat_nonneg p.val
  · exact le_refl _

theorem ModFiveThetaInput.eventually_reciprocal_padding_count_mean (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∀ᶠ L : ℝ in atTop,
      (reciprocalPaddingLaw (paddingPrimeSupply E L)).average booleanCount ≤ 4 * Real.log L := by
  filter_upwards [hP.eventually_padding_mean E] with L hL
  rw [reciprocal_padding_count_average]
  refine le_trans (sum_le_sum fun p _ => ?_) hL
  exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

theorem ModFiveThetaInput.eventually_retained_padding_probability (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∀ᶠ L : ℝ in atTop,
      (1 / 2 : ℝ) ≤ (reciprocalPaddingLaw (paddingPrimeSupply E L)).probability
        (fun b => booleanCount b ≤ 100 * Real.log L ∧
          paddingLog (paddingPrimeSupply E L) b ≤ 98 * L) := by
  filter_upwards [hP.eventually_reciprocal_padding_count_mean E,
    hP.eventually_reciprocal_padding_log_mean E, eventually_ge_atTop (2 : ℝ)]
      with L hc hl hL
  let Q := paddingPrimeSupply E L
  let μ := reciprocalPaddingLaw Q
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hlog : 0 < Real.log L := Real.log_pos (lt_of_lt_of_le (by norm_num) hL)
  have hcount : μ.probability (fun b => 100 * Real.log L < booleanCount b) ≤ 1 / 25 := by
    apply (μ.probability_lt_le_average booleanCount booleanCount_nonneg
      (100 * Real.log L) (by positivity)).trans
    calc
      _ ≤ (4 * Real.log L) / (100 * Real.log L) :=
        div_le_div_of_nonneg_right hc (by positivity)
      _ = _ := by field_simp; norm_num
  have hsize : μ.probability (fun b => 98 * L < paddingLog Q b) ≤ 2 / 49 := by
    apply (μ.probability_lt_le_average (paddingLog Q) (paddingLog_nonneg Q)
      (98 * L) (by positivity)).trans
    calc
      _ ≤ (4 * L) / (98 * L) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        change (reciprocalPaddingLaw Q).average (paddingLog Q) ≤ 4 * L
        rw [reciprocal_padding_log_average]
        exact hl
      _ = _ := by field_simp; norm_num
  have hh := μ.probability_and_ge (fun b => booleanCount b ≤ 100 * Real.log L)
    (fun b => paddingLog Q b ≤ 98 * L)
  simp only [not_le] at hh
  linarith

end TwoPointCorrelations

end OAI
