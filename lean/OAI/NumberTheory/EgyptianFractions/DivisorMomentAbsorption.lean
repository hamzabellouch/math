import Mathlib

namespace OAI
noncomputable section
open Filter Asymptotics

namespace Problem337.DivisorMomentAbsorption

/-- The large-fiber exponent is negligible compared with the quarter power. -/
theorem large_exponent_majorant_littleO (A B : ℝ) :
    (fun S : ℝ => A * (S ^ (1 / 16 : ℝ) * Real.log S) + B * Real.log S)
      =o[atTop] (fun S : ℝ => S ^ (1 / 4 : ℝ)) := by
  have hprod := (isBigO_refl (fun S : ℝ => S ^ (1 / 16 : ℝ)) atTop).mul_isLittleO
    (isLittleO_log_rpow_atTop (show (0 : ℝ) < 3 / 16 by norm_num))
  have hprod' : (fun S : ℝ => S ^ (1 / 16 : ℝ) * Real.log S)
      =o[atTop] (fun S : ℝ => S ^ (1 / 4 : ℝ)) := by
    refine hprod.congr' (Filter.Eventually.of_forall fun _ => rfl) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with S hS
    rw [← Real.rpow_add hS]
    norm_num
  exact (hprod'.const_mul_left A).add
    ((isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).const_mul_left B)

/-- A flexible final absorption step: the intermediate/small-fiber term may be
any exponential with a nonpositive exponent. -/
theorem eventually_absorb_large_contribution (A B C : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ S : ℝ in atTop, ∀ u : ℝ, u ≤ 0 →
      Real.exp (A * S ^ (1 / 16 : ℝ) * Real.log (Real.log S) + B * Real.log S) +
        2 * Real.exp u + C * Real.log S ≤ Real.exp (S ^ (1 / 4 : ℝ)) := by
  have hmajor := (large_exponent_majorant_littleO A B).bound
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hlog := ((isLittleO_log_rpow_atTop
    (show (0 : ℝ) < 1 / 4 by norm_num)).const_mul_left C).bound
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hg := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).eventually_ge_atTop 4
  filter_upwards [hmajor, hlog, hg, eventually_ge_atTop (2 : ℝ)] with S hmajor hlog hg hS
  intro u hu
  have hS0 : 0 < S := by linarith
  have hg0 : 0 ≤ S ^ (1 / 4 : ℝ) := Real.rpow_nonneg hS0.le _
  have hlog0 : 0 ≤ Real.log S := Real.log_nonneg (by linarith)
  have hmajor' : A * (S ^ (1 / 16 : ℝ) * Real.log S) + B * Real.log S ≤
      S ^ (1 / 4 : ℝ) / 2 := by
    have := (Real.le_norm_self (A * (S ^ (1 / 16 : ℝ) * Real.log S) + B * Real.log S)).trans hmajor
    simpa only [Real.norm_eq_abs, abs_of_nonneg hg0, one_div_mul_eq_div] using this
  have hlog' : C * Real.log S ≤ S ^ (1 / 4 : ℝ) / 2 := by
    have := (Real.le_norm_self (C * Real.log S)).trans hlog
    simpa only [Real.norm_eq_abs, abs_of_nonneg hg0, one_div_mul_eq_div] using this
  have hexponent : A * S ^ (1 / 16 : ℝ) * Real.log (Real.log S) + B * Real.log S ≤
      S ^ (1 / 4 : ℝ) / 2 := by
    apply le_trans _ hmajor'
    have h := mul_le_mul_of_nonneg_left (Real.log_le_self hlog0)
      (mul_nonneg hA (Real.rpow_nonneg hS0.le (1 / 16 : ℝ)))
    nlinarith
  have hE : 3 ≤ Real.exp (S ^ (1 / 4 : ℝ) / 2) := by
    have := Real.add_one_le_exp (S ^ (1 / 4 : ℝ) / 2)
    linarith
  have hu' : Real.exp u ≤ 1 := by
    simpa using Real.exp_le_exp.mpr hu
  have hC : C * Real.log S ≤ Real.exp (S ^ (1 / 4 : ℝ) / 2) :=
    hlog'.trans (by linarith [Real.add_one_le_exp (S ^ (1 / 4 : ℝ) / 2)])
  have hExp : Real.exp (A * S ^ (1 / 16 : ℝ) * Real.log (Real.log S) + B * Real.log S) ≤
      Real.exp (S ^ (1 / 4 : ℝ) / 2) := Real.exp_le_exp.mpr hexponent
  have hSquare : Real.exp (S ^ (1 / 4 : ℝ)) =
      Real.exp (S ^ (1 / 4 : ℝ) / 2) * Real.exp (S ^ (1 / 4 : ℝ) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hSquare]
  nlinarith

/-- The precise final bound used after summing the moment bands. -/
theorem eventually_divisor_moment_absorption (A B C : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ S : ℝ in atTop,
      Real.exp (A * S ^ (1 / 16 : ℝ) * Real.log (Real.log S) + B * Real.log S) +
        2 * Real.exp (-S / (200 * Real.log S)) + C * Real.log S ≤
          Real.exp (S ^ (1 / 4 : ℝ)) := by
  filter_upwards [eventually_absorb_large_contribution A B C hA,
    eventually_ge_atTop (2 : ℝ)] with S h hS
  apply h
  apply div_nonpos_of_nonpos_of_nonneg
  · linarith
  · exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))

/-- Explicit coefficients for converting the uniform large-prime class estimate
into the form required by `eventually_divisor_moment_absorption`. -/
def largeCoefficient (D r : ℝ) : ℝ :=
  r * (2 + Real.log (2 * (D + 1))) * D ^ (1 / 16 : ℝ)

def harmonicCoefficient (D C : ℝ) : ℝ :=
  C * (1 + Real.log (D + 1)) + Real.log 2

theorem large_contribution_exponent_bound (D r C S v Z : ℝ)
    (hD : 1 ≤ D) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hS : 1 ≤ S) (hlogS : 1 ≤ Real.log S) (hloglogS : 1 ≤ Real.log (Real.log S))
    (hvlo : S / (2 * Real.log S) ≤ v) (hvhi : v ≤ D * S)
    (hZ : 2 ≤ Z) (hZhi : Real.log Z ≤ D * S) :
    Real.log 2 + r * (1 + Real.log ((D + 1) * S / v)) * v ^ (1 / 16 : ℝ) +
        C * Real.log (1 + Real.log Z) ≤
      largeCoefficient D r * S ^ (1 / 16 : ℝ) * Real.log (Real.log S) +
        harmonicCoefficient D C * Real.log S := by
  have hS0 : 0 < S := by linarith
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < D + 1 := by linarith
  have hlS0 : 0 < Real.log S := by linarith
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hvlo
  have hsize : S ≤ v * (2 * Real.log S) := (div_le_iff₀ (by positivity)).1 hvlo
  have hratio : (D + 1) * S / v ≤ 2 * (D + 1) * Real.log S := by
    apply (div_le_iff₀ hv0).2
    have := mul_le_mul_of_nonneg_left hsize hE0.le
    nlinarith
  have hB : 1 + Real.log ((D + 1) * S / v) ≤
      (2 + Real.log (2 * (D + 1))) * Real.log (Real.log S) := by
    have h := Real.log_le_log (show 0 < (D + 1) * S / v by positivity) hratio
    rw [Real.log_mul (by positivity : 2 * (D + 1) ≠ 0) hlS0.ne'] at h
    have hconst : 0 ≤ 1 + Real.log (2 * (D + 1)) := by
      have := Real.log_nonneg (show 1 ≤ 2 * (D + 1) by linarith)
      linarith
    have hm := mul_le_mul_of_nonneg_left hloglogS hconst
    nlinarith
  have hpow : v ^ (1 / 16 : ℝ) ≤ D ^ (1 / 16 : ℝ) * S ^ (1 / 16 : ℝ) := by
    have h := Real.rpow_le_rpow hv0.le hvhi (show (0 : ℝ) ≤ 1 / 16 by norm_num)
    simpa only [Real.mul_rpow hD0.le hS0.le] using h
  have hcoef : 0 ≤ (2 + Real.log (2 * (D + 1))) * Real.log (Real.log S) := by
    have := Real.log_nonneg (show 1 ≤ 2 * (D + 1) by linarith)
    positivity
  have hlarge : r * (1 + Real.log ((D + 1) * S / v)) * v ^ (1 / 16 : ℝ) ≤
      largeCoefficient D r * S ^ (1 / 16 : ℝ) * Real.log (Real.log S) := by
    calc
      _ ≤ r * ((2 + Real.log (2 * (D + 1))) * Real.log (Real.log S)) *
          v ^ (1 / 16 : ℝ) := by
        gcongr
      _ ≤ r * ((2 + Real.log (2 * (D + 1))) * Real.log (Real.log S)) *
          (D ^ (1 / 16 : ℝ) * S ^ (1 / 16 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg hr hcoef)
      _ = _ := by unfold largeCoefficient; ring
  have hZ0 : 0 < 1 + Real.log Z := by
    have := Real.log_nonneg (show 1 ≤ Z by linarith)
    linarith
  have harg : 1 + Real.log Z ≤ (D + 1) * S := by nlinarith
  have hlogE : 0 ≤ Real.log (D + 1) := Real.log_nonneg (by linarith)
  have hharm : Real.log (1 + Real.log Z) ≤ (1 + Real.log (D + 1)) * Real.log S := by
    have h := Real.log_le_log hZ0 harg
    rw [Real.log_mul hE0.ne' hS0.ne'] at h
    have hm := mul_le_mul_of_nonneg_left hlogS hlogE
    nlinarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have htwo := mul_le_mul_of_nonneg_left hlogS hlog2
  have hch := mul_le_mul_of_nonneg_left hharm hC
  unfold harmonicCoefficient
  nlinarith

theorem largeCoefficient_nonneg {D r : ℝ} (hD : 1 ≤ D) (hr : 0 ≤ r) :
    0 ≤ largeCoefficient D r := by
  have := Real.log_nonneg (show 1 ≤ 2 * (D + 1) by linarith)
  unfold largeCoefficient
  positivity

theorem harmonicCoefficient_nonneg {D C : ℝ} (hD : 1 ≤ D) (hC : 0 ≤ C) :
    0 ≤ harmonicCoefficient D C := by
  have := Real.log_nonneg (show 1 ≤ D + 1 by linarith)
  have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
  unfold harmonicCoefficient
  positivity

/-- Uniform conversion of the entire large-class budget, including its factor
of two and harmonic loss. -/
theorem eventually_large_contribution_bound (D r C : ℝ)
    (hD : 1 ≤ D) (hr : 0 ≤ r) (hC : 0 ≤ C) :
    ∀ᶠ S : ℝ in atTop, ∀ v Z : ℝ,
      S / (2 * Real.log S) ≤ v → v ≤ D * S → 2 ≤ Z → Real.log Z ≤ D * S →
      2 * Real.exp (r * (1 + Real.log ((D + 1) * S / v)) * v ^ (1 / 16 : ℝ) +
          C * Real.log (1 + Real.log Z)) ≤
        Real.exp (largeCoefficient D r * S ^ (1 / 16 : ℝ) * Real.log (Real.log S) +
          harmonicCoefficient D C * Real.log S) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1]
    with S hS hlogS hloglogS
  intro v Z hvlo hvhi hZ hZhi
  have h := large_contribution_exponent_bound D r C S v Z hD hr hC
    hS hlogS hloglogS hvlo hvhi hZ hZhi
  calc
    _ = Real.exp (Real.log 2 +
        (r * (1 + Real.log ((D + 1) * S / v)) * v ^ (1 / 16 : ℝ) +
          C * Real.log (1 + Real.log Z))) := by
      rw [Real.exp_add (Real.log 2), Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Problem337.DivisorMomentAbsorption

end

end OAI
