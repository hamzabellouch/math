import OAI.NumberTheory.TwoPoint.Bounds.GoodRetainedWordSum

namespace OAI

/-! Absorb the proved good-word costs into one absolute square-root mass constant. -/

namespace TwoPointCorrelations

open Filter

private lemma positive_nat_power_exp (x : ℝ) (hx : 0 < x) (n : ℕ) :
    x ^ n = Real.exp ((n : ℝ) * Real.log x) := by
  rw [Real.exp_nat_mul, Real.exp_log hx]

/-- The threshold may depend on the fixed harmonic mass. The base
constant is absolute; the mass keeps its square-root exponent. -/
theorem eventually_good_moment_constant (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ J k S : ℕ,
      1 ≤ J → L / 2 ≤ (k : ℝ) → (S : ℝ) ≤ L ^ (1 / 4 : ℝ) →
      Real.exp (108 * L) * (2 : ℝ) ^ (4 * k * J + 2 * S) *
        Real.exp (64 * k * J) * (2 * W) ^ (J * k + S) ≤
          (Real.exp 150 * Real.sqrt W) ^ (2 * k * J) := by
  let C := 2 * Real.log 2 + Real.log (2 * W)
  have hWp : 0 < W := by linarith
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg
      (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))
      (Real.log_nonneg (by linarith))
  have hgrow := (tendsto_rpow_atTop (show 0 < (3 / 4 : ℝ) by norm_num)).eventually
    (eventually_ge_atTop (2 * C))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hgrow] with L hL hgrow
  intro J k S hJ hk hS
  have hJreal : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hkj : (k : ℝ) ≤ k * J := by nlinarith
  have hL2 : L ≤ 2 * (k : ℝ) := by linarith
  have hprod : L ^ (1 / 4 : ℝ) * L ^ (3 / 4 : ℝ) = L := by
    rw [← Real.rpow_add hL]
    norm_num
  have hCS : C * (S : ℝ) ≤ (k : ℝ) * J := by
    have hh := mul_le_mul_of_nonneg_left hgrow
      (Real.rpow_nonneg hL.le (1 / 4 : ℝ))
    rw [hprod] at hh
    have hs := mul_le_mul_of_nonneg_left hS hC
    nlinarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog : Real.log (2 * W) = Real.log 2 + Real.log W :=
    Real.log_mul (by norm_num) hWp.ne'
  have hE : 108 * L + ((4 * k * J + 2 * S : ℕ) : ℝ) * Real.log 2 +
      64 * k * J + ((J * k + S : ℕ) : ℝ) * Real.log (2 * W) ≤
      ((J * k : ℕ) : ℝ) * (300 + Real.log W) := by
    push_cast
    dsimp [C] at hCS
    rw [hlog] at hCS ⊢
    have h2 := mul_le_mul_of_nonneg_right hlog2
      (show 0 ≤ 5 * (k : ℝ) * J by positivity)
    nlinarith
  have hsq : (Real.exp 150 * Real.sqrt W) ^ 2 = Real.exp 300 * W := by
    rw [mul_pow, Real.sq_sqrt hWp.le, ← Real.exp_nat_mul]
    norm_num
  calc
    _ = Real.exp (108 * L + ((4 * k * J + 2 * S : ℕ) : ℝ) * Real.log 2 +
        64 * k * J + ((J * k + S : ℕ) : ℝ) * Real.log (2 * W)) := by
      rw [positive_nat_power_exp 2 (by norm_num),
        positive_nat_power_exp (2 * W) (by positivity), ← Real.exp_add,
        ← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (((J * k : ℕ) : ℝ) * (300 + Real.log W)) := Real.exp_le_exp.mpr hE
    _ = (Real.exp 300 * W) ^ (J * k) := by
      have he : Real.exp 300 * W = Real.exp (300 + Real.log W) := by
        rw [Real.exp_add, Real.exp_log hWp]
      rw [he, ← Real.exp_nat_mul]
    _ = (Real.exp 150 * Real.sqrt W) ^ (2 * (J * k)) := by
      exact ((pow_mul (Real.exp 150 * Real.sqrt W) 2 (J * k)).trans
        (congrArg (fun a : ℝ => a ^ (J * k)) hsq)).symm
    _ = _ := by congr 1; ring

/-- Restore the normalization factor from the padding sum. -/
theorem eventually_good_moment_with_padding (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ J k S : ℕ, ∀ K : ℝ,
      1 ≤ J → L / 2 ≤ (k : ℝ) → (S : ℝ) ≤ L ^ (1 / 4 : ℝ) → 0 ≤ K →
      Real.exp (108 * L) * (2 : ℝ) ^ (4 * k * J + 2 * S) *
        Real.exp (64 * k * J) * K ^ (2 * k) * (2 * W) ^ (J * k + S) ≤
          (K * (Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * k) := by
  filter_upwards [eventually_good_moment_constant W hW] with L hc
  intro J k S K hJ hk hS hK
  have hh := mul_le_mul_of_nonneg_right (hc J k S hJ hk hS) (pow_nonneg hK (2 * k))
  calc
    _ = (Real.exp (108 * L) * (2 : ℝ) ^ (4 * k * J + 2 * S) *
        Real.exp (64 * k * J) * (2 * W) ^ (J * k + S)) * K ^ (2 * k) := by ring
    _ ≤ (Real.exp 150 * Real.sqrt W) ^ (2 * k * J) * K ^ (2 * k) := hh
    _ = _ := by
      symm
      rw [mul_pow, ← pow_mul, show J * (2 * k) = 2 * k * J by ring, mul_comm]

end TwoPointCorrelations

end OAI
