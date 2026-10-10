import Mathlib

namespace OAI

namespace Invariant233.PhaseFailureAudit

open Filter MeasureTheory
open scoped ENNReal

theorem phase_failure_bound_eq {m : ℝ} (hm : 0 < m) :
    2 * m ^ ((4 / 5 : ℝ) * m) * (2 : ℝ) ^ m *
        (10 * m ^ (-(19 / 20 : ℝ))) ^ ((19 / 20 : ℝ) * m) =
      2 * Real.exp (-(41 / 400 : ℝ) * m * Real.log m +
        (Real.log 2 + (19 / 20 : ℝ) * Real.log 10) * m) := by
  rw [Real.rpow_def_of_pos hm, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [Real.rpow_def_of_pos (by positivity : 0 < 10 * m ^ (-(19 / 20 : ℝ)))]
  rw [Real.log_mul (by norm_num : (10 : ℝ) ≠ 0)
    (ne_of_gt (Real.rpow_pos_of_pos hm _)), Real.log_rpow hm]
  calc
    _ = 2 * (Real.exp (Real.log m * ((4 / 5 : ℝ) * m)) *
        Real.exp (Real.log 2 * m) *
        Real.exp ((Real.log 10 + (-(19 / 20 : ℝ)) * Real.log m) *
          ((19 / 20 : ℝ) * m))) := by ring
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      ring

theorem summable_exp_neg_mul_log {c C : ℝ} (hc : 0 < c)
    (m : ℕ → ℝ) (hm : ∀ j : ℕ, (j : ℝ) ≤ m j) :
    Summable (fun j => Real.exp (-c * m j * Real.log (m j) + C * m j)) := by
  have hmtop : Tendsto m atTop atTop :=
    tendsto_atTop_mono hm tendsto_natCast_atTop_atTop
  have hlogtop : Tendsto (fun j => Real.log (m j)) atTop atTop :=
    Real.tendsto_log_atTop.comp hmtop
  have hlog : ∀ᶠ j in atTop, (C + 1) / c ≤ Real.log (m j) :=
    hlogtop.eventually_ge_atTop _
  have hs : Summable (fun j => Real.exp (-m j)) := by
    simpa only [neg_one_mul] using
      (Real.summable_exp_nat_mul_of_ge (by norm_num : (-1 : ℝ) < 0) hm)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [hlog] with j hj
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hm0 : 0 ≤ m j := le_trans (Nat.cast_nonneg j) (hm j)
  have hcj : C + 1 ≤ c * Real.log (m j) := by
    have := (div_le_iff₀ hc).mp hj
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcj hm0
  nlinarith

theorem summable_phase_failure_bound (m : ℕ → ℝ)
    (hmpos : ∀ j, 0 < m j) (hm : ∀ j : ℕ, (j : ℝ) ≤ m j) :
    Summable (fun j => 2 * (m j) ^ ((4 / 5 : ℝ) * m j) * (2 : ℝ) ^ m j *
      (10 * (m j) ^ (-(19 / 20 : ℝ))) ^ ((19 / 20 : ℝ) * m j)) := by
  simp_rw [phase_failure_bound_eq (hmpos _)]
  exact (summable_exp_neg_mul_log (by norm_num : (0 : ℝ) < 41 / 400)
    m hm).mul_left 2

theorem summable_phase_failure_bound_nat (m : ℕ → ℕ)
    (hm : ∀ j, 2 ^ j ≤ m j) :
    Summable (fun j => 2 * (m j : ℝ) ^ ((4 / 5 : ℝ) * m j) * (2 : ℝ) ^ m j *
      (10 * (m j : ℝ) ^ (-(19 / 20 : ℝ))) ^ ((19 / 20 : ℝ) * m j)) := by
  have hmpos : ∀ j, 0 < (m j : ℝ) := by
    intro j
    exact_mod_cast lt_of_lt_of_le (by positivity : 0 < 2 ^ j) (hm j)
  have hmindex : ∀ j : ℕ, (j : ℝ) ≤ (m j : ℝ) := by
    intro j
    exact_mod_cast (le_trans (Nat.le_of_lt Nat.lt_two_pow_self) (hm j))
  simpa only [Real.rpow_natCast] using
    summable_phase_failure_bound (fun j => (m j : ℝ)) hmpos hmindex

theorem ae_eventually_notMem_of_phase_failure_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (bad : ℕ → Set Ω)
    (m : ℕ → ℕ) (hm : ∀ j, 2 ^ j ≤ m j)
    (hbad : ∀ j, μ (bad j) ≤ ENNReal.ofReal
      (2 * (m j : ℝ) ^ ((4 / 5 : ℝ) * m j) * (2 : ℝ) ^ m j *
        (10 * (m j : ℝ) ^ (-(19 / 20 : ℝ))) ^ ((19 / 20 : ℝ) * m j))) :
    ∀ᵐ ω ∂μ, ∀ᶠ j in atTop, ω ∉ bad j := by
  apply MeasureTheory.ae_eventually_notMem
  exact ne_top_of_le_ne_top (summable_phase_failure_bound_nat m hm).tsum_ofReal_ne_top
    (ENNReal.tsum_le_tsum hbad)

end Invariant233.PhaseFailureAudit

end OAI
