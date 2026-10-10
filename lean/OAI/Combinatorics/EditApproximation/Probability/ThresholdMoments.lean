import OAI.Combinatorics.EditApproximation.Geometry.Seed

namespace OAI

/-!
# Discrete threshold moments

The initial estimator samples an integer uniformly from `1, …, B`.
The finite count below proves its rounding bias exactly; no continuous
threshold distribution is substituted for the executable sampler.
-/

namespace EditApproximation

open Finset

theorem threshold_count (B : ℕ) (scale value : ℝ)
    (hB : 0 < B) (hscale : 0 < scale) (hvalue : 0 ≤ value) (hupper : value < scale) :
    ((Icc 1 B).filter fun (r : ℕ) => scale * (r : ℝ) / B ≤ value).card =
      ⌊(B : ℝ) * value / scale⌋₊ := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hq : 0 ≤ (B : ℝ) * value / scale := by positivity
  have hqB : (B : ℝ) * value / scale < B := by
    apply (div_lt_iff₀ hscale).2
    nlinarith
  have hfloor : ⌊(B : ℝ) * value / scale⌋₊ < B := (Nat.floor_lt hq).2 hqB
  have hiff (r : ℕ) : scale * r / B ≤ value ↔ r ≤ ⌊(B : ℝ) * value / scale⌋₊ := by
    rw [Nat.le_floor_iff hq, div_le_iff₀ hBr, le_div_iff₀ hscale]
    constructor <;> intro h <;> nlinarith
  have hfilter : (Icc 1 B).filter (fun (r : ℕ) => scale * (r : ℝ) / B ≤ value) =
      Icc 1 ⌊(B : ℝ) * value / scale⌋₊ := by
    ext r
    simp only [mem_filter, mem_Icc, hiff]
    constructor
    · intro h
      exact ⟨h.1.1, h.2⟩
    · intro h
      exact ⟨⟨h.1, h.2.trans hfloor.le⟩, h.2⟩
  rw [hfilter]
  simp only [Nat.card_Icc, Nat.add_sub_cancel]

/-- Exact discrete first moment below the scale; dividing the sum by `B`
gives `scale * floor(B * value / scale) / B`. -/
theorem threshold_sum (B : ℕ) (scale value : ℝ)
    (hB : 0 < B) (hscale : 0 < scale) (hvalue : 0 ≤ value) (hupper : value < scale) :
    (∑ r ∈ Icc 1 B, thresholdContribution (scale * r / B) scale value) =
      (⌊(B : ℝ) * value / scale⌋₊ : ℝ) * scale := by
  have hpoint (r : ℕ) : thresholdContribution (scale * r / B) scale value =
      if scale * r / B ≤ value then scale else 0 := by
    simp only [thresholdContribution, max_eq_right hupper.le]
  simp_rw [hpoint]
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul,
    threshold_count B scale value hB hscale hvalue hupper]

/-- Bias bound used in the coarse estimator: the discrete mean is below
the true argument by at most one grid unit. -/
theorem threshold_bias (B : ℕ) (scale value : ℝ)
    (hB : 0 < B) (hscale : 0 < scale) (hvalue : 0 ≤ value) (hupper : value < scale) :
    0 ≤ value - (∑ r ∈ Icc 1 B,
      thresholdContribution (scale * r / B) scale value) / B ∧
    value - (∑ r ∈ Icc 1 B,
      thresholdContribution (scale * r / B) scale value) / B ≤ scale / B := by
  rw [threshold_sum B scale value hB hscale hvalue hupper]
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hq : 0 ≤ (B : ℝ) * value / scale := by positivity
  have hflo := Nat.floor_le hq
  have hfhi := Nat.lt_floor_add_one ((B : ℝ) * value / scale)
  have hl := (le_div_iff₀ hscale).1 hflo
  have hh := (div_lt_iff₀ hscale).1 hfhi
  constructor
  · apply sub_nonneg.mpr
    exact (div_le_iff₀ hBr).2 (by nlinarith)
  · apply (le_div_iff₀ hBr).2
    have hid : (value - (⌊(B : ℝ) * value / scale⌋₊ : ℝ) * scale / B) * B =
        value * B - (⌊(B : ℝ) * value / scale⌋₊ : ℝ) * scale := by
      field_simp
    rw [hid]
    nlinarith

theorem uniform_centered_square_identity {ι : Type*} (samples : Finset ι)
    (value : ι → ℝ) (hcard : 0 < samples.card) :
    (∑ i ∈ samples, (value i - (∑ j ∈ samples, value j) / samples.card) ^ 2) /
        samples.card =
      (∑ i ∈ samples, value i ^ 2) / samples.card -
        ((∑ i ∈ samples, value i) / samples.card) ^ 2 := by
  let mean := (∑ i ∈ samples, value i) / samples.card
  have hcardr : (0 : ℝ) < samples.card := by exact_mod_cast hcard
  have hexpand : (∑ i ∈ samples, (value i - mean) ^ 2) =
      (∑ i ∈ samples, value i ^ 2) - 2 * mean * (∑ i ∈ samples, value i) +
        (samples.card : ℝ) * mean ^ 2 := by
    calc
      _ = ∑ i ∈ samples, (value i ^ 2 - 2 * mean * value i + mean ^ 2) :=
        sum_congr rfl fun _ _ => by ring
      _ = _ := by
        rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
  change (∑ i ∈ samples, (value i - mean) ^ 2) / samples.card = _
  rw [hexpand]
  dsimp [mean]
  field_simp
  ring

/-- The centered second moment of the actual finite threshold sampler is
at most `scale * value`, as used in the Bernstein variance proxy. -/
theorem threshold_variance_bound (B : ℕ) (scale value : ℝ)
    (hB : 0 < B) (hscale : 0 < scale) (hvalue : 0 ≤ value) (hupper : value < scale) :
    (∑ r ∈ Icc 1 B,
      (thresholdContribution (scale * r / B) scale value -
        (∑ s ∈ Icc 1 B, thresholdContribution (scale * s / B) scale value) / B) ^ 2) / B ≤
      scale * value := by
  have hcard : (Icc 1 B).card = B := by simp only [Nat.card_Icc, Nat.add_sub_cancel]
  have hvariance := uniform_centered_square_identity (Icc 1 B)
    (fun r => thresholdContribution (scale * r / B) scale value) (by omega)
  rw [hcard] at hvariance
  rw [hvariance]
  have hpoint (r : ℕ) : thresholdContribution (scale * r / B) scale value ^ 2 =
      scale * thresholdContribution (scale * r / B) scale value := by
    simp only [thresholdContribution, max_eq_right hupper.le]
    split_ifs <;> ring
  simp_rw [hpoint]
  rw [← mul_sum, mul_div_assoc]
  have hmean := (threshold_bias B scale value hB hscale hvalue hupper).1
  have hscaled := mul_le_mul_of_nonneg_left (sub_nonneg.mp hmean) hscale.le
  nlinarith [sq_nonneg ((∑ r ∈ Icc 1 B,
    thresholdContribution (scale * r / B) scale value) / B)]

end EditApproximation

end OAI
