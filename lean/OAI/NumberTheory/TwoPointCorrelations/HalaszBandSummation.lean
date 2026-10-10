import OAI.NumberTheory.TwoPointCorrelations.HalaszBandPartition

namespace OAI

/-! Summing the minimum of the trivial band estimate and the distance
estimate. This is the step that keeps the factor (M+1) exp(-M). -/

namespace TwoPointCorrelations

open Finset

lemma halasz_band_scale_sum (J : ℕ) :
    (∑ j ∈ range J, halaszBandScale j) = Real.log 2 * ((2 : ℝ) ^ J - 1) := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [sum_range_succ, ih]
      simp only [halaszBandScale, pow_succ]
      ring

lemma halasz_band_scale_sum_le (J : ℕ) :
    (∑ j ∈ range J, halaszBandScale j) ≤ halaszBandScale J := by
  rw [halasz_band_scale_sum]
  dsimp [halaszBandScale]
  have htwo := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  nlinarith

lemma halasz_band_inverse_sum (J : ℕ) :
    (∑ j ∈ range J, (halaszBandScale j)⁻¹) =
      (2 / Real.log 2) * (1 - ((2 : ℝ)⁻¹) ^ J) := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [sum_range_succ, ih]
      simp only [halaszBandScale, mul_inv_rev, inv_pow, pow_succ]
      ring

lemma halasz_band_inverse_sum_le (J : ℕ) :
    (∑ j ∈ range J, (halaszBandScale j)⁻¹) ≤ 2 / Real.log 2 := by
  rw [halasz_band_inverse_sum]
  have htwo : 0 ≤ 2 / Real.log 2 := by positivity
  have hp : 0 ≤ ((2 : ℝ)⁻¹) ^ J := by positivity
  nlinarith

lemma halasz_band_min_split {A : ℝ} (_hA : 0 ≤ A) (J k : ℕ) (hk : k ≤ J) :
    (∑ j ∈ range J, min A (halaszBandScale j)) ≤
      halaszBandScale k + (J - k : ℕ) * A := by
  rw [← sum_range_add_sum_Ico _ hk]
  have hfirst : (∑ j ∈ range k, min A (halaszBandScale j)) ≤ halaszBandScale k :=
    (sum_le_sum (fun j _ => min_le_right _ _)).trans (halasz_band_scale_sum_le k)
  have hlast : (∑ j ∈ Ico k J, min A (halaszBandScale j)) ≤ (J - k : ℕ) * A := by
    apply (sum_le_sum (fun j _ => min_le_left _ _)).trans_eq
    simp
  exact add_le_add hfirst hlast

theorem halasz_band_saving_sum : ∃ C : ℝ, 0 < C ∧
    ∀ (J : ℕ) (V M : ℝ), 0 ≤ V → 0 ≤ M → halaszBandScale J ≤ 2 * V →
      (∑ j ∈ range J, min (V * Real.exp (-M)) (halaszBandScale j)) ≤
        C * V * (M + 1) * Real.exp (-M) := by
  let C := 1 / Real.log 2 + 3
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro J V M hV hM htop
  let r : ℕ := ⌈M / Real.log 2⌉₊
  let A := V * Real.exp (-M)
  have hA : 0 ≤ A := mul_nonneg hV (Real.exp_pos _).le
  have hrlo : M / Real.log 2 ≤ (r : ℝ) := Nat.le_ceil _
  have hrhi : (r : ℝ) < M / Real.log 2 + 1 := Nat.ceil_lt_add_one (div_nonneg hM htwo.le)
  have hpow : Real.exp M ≤ (2 : ℝ) ^ r := by
    have h := Real.exp_le_exp.mpr ((div_le_iff₀ htwo).mp hrlo)
    simpa only [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
  have hsum : (∑ j ∈ range J, min A (halaszBandScale j)) ≤ ((r : ℝ) + 2) * A := by
    by_cases hrJ : r ≤ J
    · have hscale : halaszBandScale (J - r) ≤ 2 * A := by
        have hmul : halaszBandScale (J - r) * (2 : ℝ) ^ r = halaszBandScale J := by
          dsimp [halaszBandScale]
          rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hrJ]
        calc
          _ = halaszBandScale J / (2 : ℝ) ^ r := by rw [← hmul]; field_simp
          _ ≤ 2 * V / (2 : ℝ) ^ r := div_le_div_of_nonneg_right htop (by positivity)
          _ ≤ 2 * V / Real.exp M := div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hpow
          _ = 2 * A := by dsimp [A]; rw [Real.exp_neg]; ring
      have hs := halasz_band_min_split hA J (J - r) (Nat.sub_le _ _)
      have hcard : J - (J - r) = r := Nat.sub_sub_self hrJ
      rw [hcard] at hs
      nlinarith
    · have hcount : (J : ℝ) ≤ r := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hrJ))
      have hs : (∑ j ∈ range J, min A (halaszBandScale j)) ≤ (J : ℝ) * A := by
        apply (sum_le_sum (fun j _ => min_le_left _ _)).trans_eq
        simp
      nlinarith
  have hlinear : (r : ℝ) + 2 ≤ C * (M + 1) := by
    have hi : 0 ≤ 1 / Real.log 2 := by positivity
    dsimp [C]
    rw [div_eq_mul_inv] at hrhi
    simp only [one_div] at hi ⊢
    nlinarith
  calc
    _ ≤ ((r : ℝ) + 2) * A := hsum
    _ ≤ (C * (M + 1)) * A := mul_le_mul_of_nonneg_right hlinear hA
    _ = _ := by dsimp [A]; ring

end TwoPointCorrelations

end OAI
