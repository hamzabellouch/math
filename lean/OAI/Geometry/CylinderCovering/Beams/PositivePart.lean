import Mathlib

namespace OAI

open Set MeasureTheory
noncomputable section
namespace CylinderCovering.BeamPositivePart

lemma positive_on_core {a R t B : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hR2 : R ^ 2 = 1 / 2) (ht0 : 0 ≤ t) (htR : t ≤ R) (hB : 0 ≤ B) :
    0 ≤ a * (1 - 2 * t ^ 2) + a ^ 2 * B := by
  have ht2 : t ^ 2 ≤ R ^ 2 := (sq_le_sq₀ ht0 hR).mpr htR
  exact add_nonneg (mul_nonneg ha (by nlinarith)) (mul_nonneg (sq_nonneg _) hB)

lemma positivePart_le_after_root {a R t B : ℝ} (ha : 0 ≤ a)
    (hR : 0 ≤ R) (hR2 : R ^ 2 = 1 / 2) (htR : R ≤ t) (hB : B ≤ 3) :
    max (a * (1 - 2 * t ^ 2) + a ^ 2 * B) 0 ≤ 3 * a ^ 2 := by
  have ht2 : R ^ 2 ≤ t ^ 2 := (sq_le_sq₀ hR (hR.trans htR)).mpr htR
  apply max_le
  · have h1 := mul_nonpos_of_nonneg_of_nonpos ha (show 1 - 2 * t ^ 2 ≤ 0 by nlinarith)
    have h2 := mul_le_mul_of_nonneg_left hB (sq_nonneg a)
    nlinarith only [h1, h2]
  · positivity

lemma positivePart_zero_after_collar {a R t B : ℝ} (ha : 0 ≤ a)
    (hR : 1 / 2 ≤ R) (hR2 : R ^ 2 = 1 / 2)
    (ht : R + 3 * a ≤ t) (hB : B ≤ 3) :
    max (a * (1 - 2 * t ^ 2) + a ^ 2 * B) 0 = 0 := by
  have htR : R ≤ t := by linarith
  have hproduct : 3 * a ≤ (t - R) * (t + R) := by
    calc
      3 * a ≤ (t - R) * 1 := by linarith
      _ ≤ (t - R) * (t + R) :=
        mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr htR)
  have hlead : 1 - 2 * t ^ 2 ≤ -6 * a := by nlinarith [hproduct]
  have h1 := mul_le_mul_of_nonneg_left hlead ha
  have h2 := mul_le_mul_of_nonneg_left hB (sq_nonneg a)
  apply max_eq_right
  nlinarith only [h1, h2, sq_nonneg a]

theorem integral_support_error {a R : ℝ} (B : ℝ → ℝ) (hBc : Continuous B)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 12)
    (hR0 : 1 / 2 ≤ R) (hR1 : R ≤ 3 / 4) (hR2 : R ^ 2 = 1 / 2)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ B t ∧ B t ≤ 3) :
    0 ≤ (∫ t in (0 : ℝ)..1, max (a * (1 - 2 * t ^ 2) + a ^ 2 * B t) 0) -
      (∫ t in (0 : ℝ)..R, a * (1 - 2 * t ^ 2) + a ^ 2 * B t) ∧
    (∫ t in (0 : ℝ)..1, max (a * (1 - 2 * t ^ 2) + a ^ 2 * B t) 0) -
      (∫ t in (0 : ℝ)..R, a * (1 - 2 * t ^ 2) + a ^ 2 * B t) ≤ 9 * a ^ 3 := by
  let q : ℝ → ℝ := fun t => a * (1 - 2 * t ^ 2) + a ^ 2 * B t
  let f : ℝ → ℝ := fun t => max (q t) 0
  let c := R + 3 * a
  have hq : Continuous q := by fun_prop
  have hf : Continuous f := hq.max continuous_const
  have hR : 0 ≤ R := by linarith
  have hRc : R ≤ c := by dsimp [c]; linarith
  have hc1 : c ≤ 1 := by dsimp [c]; linarith
  have hcore : (∫ t in (0 : ℝ)..R, f t) = ∫ t in (0 : ℝ)..R, q t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hR] at ht
    unfold f
    apply max_eq_left
    exact positive_on_core ha0 hR hR2 ht.1 ht.2 (hB t ⟨ht.1, by linarith [ht.2]⟩).1
  have htail : (∫ t in c..1, f t) = 0 := by
    calc
      _ = ∫ _t in c..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hc1] at ht
        exact positivePart_zero_after_collar ha0 hR0 hR2 ht.1
          (hB t ⟨by linarith [ht.1], ht.2⟩).2
      _ = 0 := by simp
  have hsplit : (∫ t in (0 : ℝ)..1, f t) - (∫ t in (0 : ℝ)..R, q t) =
      ∫ t in R..c, f t := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := volume) 0 R) (hf.intervalIntegrable (μ := volume) R c)
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := volume) 0 c) (hf.intervalIntegrable (μ := volume) c 1)
    rw [htail] at h2
    rw [hcore] at h1
    linarith only [h1, h2]
  change 0 ≤ (∫ t in (0 : ℝ)..1, f t) - (∫ t in (0 : ℝ)..R, q t) ∧
    (∫ t in (0 : ℝ)..1, f t) - (∫ t in (0 : ℝ)..R, q t) ≤ 9 * a ^ 3
  rw [hsplit]
  constructor
  · exact intervalIntegral.integral_nonneg_of_forall hRc (fun t => le_max_right _ _)
  · calc
      (∫ t in R..c, f t) ≤ ∫ _t in R..c, 3 * a ^ 2 := by
        apply intervalIntegral.integral_mono_on hRc (hf.intervalIntegrable R c) (continuous_const.intervalIntegrable R c)
        intro t ht
        exact positivePart_le_after_root ha0 hR hR2 ht.1
          (hB t ⟨hR.trans ht.1, ht.2.trans hc1⟩).2
      _ = 9 * a ^ 3 := by simp [c]; ring

lemma source_coefficient_bounds {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ t ^ 2 * (1 + (1 - t) ^ 2 + t ^ 2) ∧
      t ^ 2 * (1 + (1 - t) ^ 2 + t ^ 2) ≤ 3 := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have hs2 : (1 - t) ^ 2 ≤ 1 := by nlinarith
  constructor
  · positivity
  · have hsum : 1 + (1 - t) ^ 2 + t ^ 2 ≤ 3 := by linarith
    have hm := mul_le_mul ht2 hsum (by positivity : 0 ≤ 1 + (1 - t) ^ 2 + t ^ 2)
      (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [hm]

theorem source_integral_support_error {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 12) :
    |(∫ t in (0 : ℝ)..1,
      max (a * (1 - 2 * t ^ 2) + a ^ 2 * (t ^ 2 * (1 + (1 - t) ^ 2 + t ^ 2))) 0) -
      (∫ t in (0 : ℝ)..(1 / Real.sqrt 2),
        a * (1 - 2 * t ^ 2) + a ^ 2 * (t ^ 2 * (1 + (1 - t) ^ 2 + t ^ 2)))| ≤
      9 * a ^ 3 := by
  have hR : (0 : ℝ) ≤ 1 / Real.sqrt 2 := by positivity
  have hR2 : (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) := by norm_num [div_pow]
  have h := integral_support_error (fun t => t ^ 2 * (1 + (1 - t) ^ 2 + t ^ 2))
    (by fun_prop) ha0 ha1 (by nlinarith) (by nlinarith) hR2
    (fun t ht => source_coefficient_bounds ht.1 ht.2)
  rw [abs_of_nonneg h.1]
  exact h.2

end CylinderCovering.BeamPositivePart

end

end OAI
