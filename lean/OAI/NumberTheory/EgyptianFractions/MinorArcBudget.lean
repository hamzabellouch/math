import Mathlib

namespace OAI
noncomputable section
open Filter Asymptotics

namespace Problem337.ThreePrimeAnalysis

/-- Explicit arithmetic loss budget for a standard Vaughan-type envelope.
This is a scalar inequality: it does not assume or assert an exponential-sum
estimate for primes. -/
theorem vaughan_envelope_le_log_budget (N q C : ℝ)
    (hN : 1 < N) (hC : 0 ≤ C)
    (hconstant : 3 * C ≤ Real.log N ^ 2)
    (hsmall : Real.log N ^ 11 ≤ N ^ (1 / 5 : ℝ))
    (hqlow : Real.log N ^ 22 ≤ q)
    (hqup : q ≤ N / Real.log N ^ 22) :
    C * (N / Real.sqrt q + N ^ (4 / 5 : ℝ) + Real.sqrt (N * q)) *
        Real.log N ^ 4 ≤ N / Real.log N ^ 5 := by
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos hN
  have hT : 0 < Real.log N ^ 11 := pow_pos hL _
  have hrootlower : Real.log N ^ 11 ≤ Real.sqrt q := by
    apply Real.le_sqrt_of_sq_le
    simpa only [← pow_mul] using hqlow
  have hfirst : N / Real.sqrt q ≤ N / Real.log N ^ 11 :=
    div_le_div_of_nonneg_left hN0.le hT hrootlower
  have hthird : Real.sqrt (N * q) ≤ N / Real.log N ^ 11 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨(div_pos hN0 hT).le, ?_⟩
    have hm := mul_le_mul_of_nonneg_left hqup hN0.le
    calc
      N * q ≤ N * (N / Real.log N ^ 22) := hm
      _ = (N / Real.log N ^ 11) ^ 2 := by ring
  have hmiddle : N ^ (4 / 5 : ℝ) ≤ N / Real.log N ^ 11 := by
    apply (le_div_iff₀ hT).mpr
    calc
      N ^ (4 / 5 : ℝ) * Real.log N ^ 11 ≤
          N ^ (4 / 5 : ℝ) * N ^ (1 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hN0.le _)
      _ = N := by rw [← Real.rpow_add hN0]; norm_num
  have hsum : N / Real.sqrt q + N ^ (4 / 5 : ℝ) + Real.sqrt (N * q) ≤
      3 * (N / Real.log N ^ 11) := by linarith
  have hmajor := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsum hC) (pow_nonneg hL.le 4)
  calc
    _ ≤ C * (3 * (N / Real.log N ^ 11)) * Real.log N ^ 4 := hmajor
    _ = (3 * C) * (N / Real.log N ^ 7) := by field_simp
    _ ≤ Real.log N ^ 2 * (N / Real.log N ^ 7) :=
      mul_le_mul_of_nonneg_right hconstant (by positivity)
    _ = N / Real.log N ^ 5 := by field_simp

/-- A fixed envelope coefficient is absorbed uniformly over the entire minor
rational-denominator window. The onset depends only on `C`. -/
theorem eventually_vaughan_envelope_le_log_budget (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ N : ℝ in atTop, ∀ q : ℝ,
      Real.log N ^ 22 ≤ q → q ≤ N / Real.log N ^ 22 →
      C * (N / Real.sqrt q + N ^ (4 / 5 : ℝ) + Real.sqrt (N * q)) *
        Real.log N ^ 4 ≤ N / Real.log N ^ 5 := by
  have hlittle : (fun N : ℝ => Real.log N ^ 11) =o[atTop]
      (fun N : ℝ => N ^ (1 / 5 : ℝ)) := by
    simpa only [Real.rpow_ofNat] using
      (isLittleO_log_rpow_rpow_atTop (11 : ℝ) (by norm_num : (0 : ℝ) < 1 / 5))
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (3 * C + 1),
    hlittle.bound (by norm_num : (0 : ℝ) < 1)] with N hN hlog hsmall
  have hL : 0 < Real.log N := Real.log_pos hN
  have hlog1 : 1 ≤ Real.log N := by linarith
  have hconstant : 3 * C ≤ Real.log N ^ 2 := by nlinarith
  have hsmall' : Real.log N ^ 11 ≤ N ^ (1 / 5 : ℝ) := by
    simpa only [Real.norm_of_nonneg (pow_nonneg hL.le 11),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ N) _), one_mul] using hsmall
  intro q hqlow hqup
  exact vaughan_envelope_le_log_budget N q C hN hC hconstant hsmall' hqlow hqup

/-- Combining a `N/log(N)^5` pointwise minor-arc bound with any fixed
`A*N*log(N)` energy budget gives an arbitrarily small quadratic error. -/
theorem eventually_minor_cubic_log_budget (A ε : ℝ) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∀ᶠ N : ℝ in atTop,
      (N / Real.log N ^ 5) * (A * N * Real.log N) ≤ ε * N ^ 2 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 + A / ε)] with N hN hlog
  have hL : 0 < Real.log N := Real.log_pos hN
  have hL1 : 1 ≤ Real.log N := by linarith [div_nonneg hA hε.le]
  have hLpow : Real.log N ≤ Real.log N ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 (show 1 ≤ 4 by omega)
  have hratio : A / ε ≤ Real.log N ^ 4 := by linarith
  have hcoef : A / Real.log N ^ 4 ≤ ε := by
    apply (div_le_iff₀ (pow_pos hL 4)).mpr
    have ha := (div_le_iff₀ hε).mp hratio
    simpa only [mul_comm] using ha
  calc
    _ = (A / Real.log N ^ 4) * N ^ 2 := by field_simp
    _ ≤ ε * N ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg N)

/-- Variable logarithmic losses need only a correspondingly wider rational
cutoff. This form is useful when a coefficient moment yields an unspecified
but fixed power of the logarithm. -/
theorem vaughan_envelope_le_power_log_budget (B D : ℕ) (N q C : ℝ)
    (hN : 1 < N) (hC : 0 ≤ C)
    (hconstant : 3 * C ≤ Real.log N ^ 2)
    (hsmall : Real.log N ^ (B + D + 2) ≤ N ^ (1 / 5 : ℝ))
    (hqlow : Real.log N ^ (2 * (B + D + 2)) ≤ q)
    (hqup : q ≤ N / Real.log N ^ (2 * (B + D + 2))) :
    C * (N / Real.sqrt q + N ^ (4 / 5 : ℝ) + Real.sqrt (N * q)) *
        Real.log N ^ B ≤ N / Real.log N ^ D := by
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos hN
  have hT : 0 < Real.log N ^ (B + D + 2) := pow_pos hL _
  have hpower : Real.log N ^ (2 * (B + D + 2)) =
      (Real.log N ^ (B + D + 2)) ^ 2 := by rw [Nat.mul_comm, pow_mul]
  have hrootlower : Real.log N ^ (B + D + 2) ≤ Real.sqrt q := by
    apply Real.le_sqrt_of_sq_le
    simpa only [hpower] using hqlow
  have hfirst : N / Real.sqrt q ≤ N / Real.log N ^ (B + D + 2) :=
    div_le_div_of_nonneg_left hN0.le hT hrootlower
  have hthird : Real.sqrt (N * q) ≤ N / Real.log N ^ (B + D + 2) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨(div_pos hN0 hT).le, ?_⟩
    calc
      N * q ≤ N * (N / Real.log N ^ (2 * (B + D + 2))) :=
        mul_le_mul_of_nonneg_left hqup hN0.le
      _ = (N / Real.log N ^ (B + D + 2)) ^ 2 := by rw [hpower]; ring
  have hmiddle : N ^ (4 / 5 : ℝ) ≤ N / Real.log N ^ (B + D + 2) := by
    apply (le_div_iff₀ hT).mpr
    calc
      N ^ (4 / 5 : ℝ) * Real.log N ^ (B + D + 2) ≤
          N ^ (4 / 5 : ℝ) * N ^ (1 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hN0.le _)
      _ = N := by rw [← Real.rpow_add hN0]; norm_num
  have hsum : N / Real.sqrt q + N ^ (4 / 5 : ℝ) + Real.sqrt (N * q) ≤
      3 * (N / Real.log N ^ (B + D + 2)) := by linarith
  have hmajor := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsum hC) (pow_nonneg hL.le B)
  calc
    _ ≤ C * (3 * (N / Real.log N ^ (B + D + 2))) * Real.log N ^ B := hmajor
    _ = (3 * C) * (N / Real.log N ^ (D + 2)) := by
      rw [show B + D + 2 = B + (D + 2) by omega, pow_add]
      field_simp
    _ ≤ Real.log N ^ 2 * (N / Real.log N ^ (D + 2)) :=
      mul_le_mul_of_nonneg_right hconstant (by positivity)
    _ = N / Real.log N ^ D := by rw [pow_add]; field_simp

/-- Any fixed polynomial logarithmic loss has a uniform minor-window budget.
Neither the fixed log exponents nor the implied constant depend on `N` or `q`. -/
theorem eventually_vaughan_envelope_le_power_log_budget (B D : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ N : ℝ in atTop, ∀ q : ℝ,
      Real.log N ^ (2 * (B + D + 2)) ≤ q →
      q ≤ N / Real.log N ^ (2 * (B + D + 2)) →
      C * (N / Real.sqrt q + N ^ (4 / 5 : ℝ) + Real.sqrt (N * q)) *
        Real.log N ^ B ≤ N / Real.log N ^ D := by
  have hlittle : (fun N : ℝ => Real.log N ^ (B + D + 2)) =o[atTop]
      (fun N : ℝ => N ^ (1 / 5 : ℝ)) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop ((B + D + 2 : ℕ) : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 5))
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (3 * C + 1),
    hlittle.bound (by norm_num : (0 : ℝ) < 1)] with N hN hlog hsmall
  have hL : 0 < Real.log N := Real.log_pos hN
  have hlog1 : 1 ≤ Real.log N := by linarith
  have hconstant : 3 * C ≤ Real.log N ^ 2 := by nlinarith
  have hsmall' : Real.log N ^ (B + D + 2) ≤ N ^ (1 / 5 : ℝ) := by
    simpa only [Real.norm_of_nonneg (pow_nonneg hL.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ N) _), one_mul] using hsmall
  intro q hqlow hqup
  exact vaughan_envelope_le_power_log_budget B D N q C hN hC hconstant hsmall' hqlow hqup

end Problem337.ThreePrimeAnalysis

end

end OAI
