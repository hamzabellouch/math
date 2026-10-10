import Mathlib
import OAI.Analysis.IrrationalRotation.Model.PhaseFailure

namespace OAI

open Filter MeasureTheory
open scoped ENNReal Topology

namespace Invariant233.ProductPhases

theorem failureBound_nonneg {m : ℝ} (hm : 0 ≤ m) : 0 ≤ failureBound m := by
  unfold failureBound
  positivity

theorem ten_mul_phaseWidth_le_one {m : ℝ} (hm : 100 ≤ m) :
    10 * m ^ (-19 / 20 : ℝ) ≤ 1 := by
  have hm0 : 0 ≤ m := by linarith
  have hs : (10 : ℝ) ≤ Real.sqrt m := by
    nlinarith [Real.sq_sqrt hm0, Real.sqrt_nonneg m]
  have hb : m ^ (-19 / 20 : ℝ) ≤ (10 : ℝ)⁻¹ := by
    calc
      m ^ (-19 / 20 : ℝ) ≤ m ^ (-(1 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = (Real.sqrt m)⁻¹ := by rw [Real.rpow_neg hm0, ← Real.sqrt_eq_rpow]
      _ ≤ (10 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hs
  nlinarith

theorem failureBound_eq_exp {m : ℝ} (hm : 0 < m) :
    failureBound m = 2 * Real.exp (-(41 / 400 : ℝ) * m * Real.log m +
      (Real.log 2 + (19 / 20 : ℝ) * Real.log 10) * m) := by
  unfold failureBound
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 10) (Real.rpow_nonneg hm.le _),
    ← Real.rpow_mul hm.le]
  simp only [Real.rpow_def_of_pos hm,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 10)]
  rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

theorem eventually_failureBound_le_exp :
    ∀ᶠ m : ℝ in atTop, failureBound m ≤ Real.exp (-m) := by
  let C : ℝ := Real.log 2 + (19 / 20 : ℝ) * Real.log 10
  have hl : ∀ᶠ m : ℝ in atTop,
      (400 / 41 : ℝ) * (C + 2) ≤ Real.log m :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (Real.log 2), hl]
    with m hm hm2 hlog
  rw [failureBound_eq_exp (by linarith)]
  have he : -(41 / 400 : ℝ) * m * Real.log m + C * m ≤ -2 * m := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlog) (show 0 ≤ m by linarith)]
  calc
    2 * Real.exp (-(41 / 400 : ℝ) * m * Real.log m + C * m) =
        Real.exp (Real.log 2 + (-(41 / 400 : ℝ) * m * Real.log m + C * m)) := by
      conv_rhs => rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (-m) := Real.exp_le_exp.mpr (by linarith)

theorem summable_failureBound_of_nat_le {m : ℕ → ℝ}
    (hm : ∀ j : ℕ, (j : ℝ) ≤ m j) (hmnonneg : ∀ j, 0 ≤ m j) :
    Summable (fun j => failureBound (m j)) := by
  have hmtop : Tendsto m atTop atTop :=
    tendsto_atTop_mono hm tendsto_natCast_atTop_atTop
  have hb := hmtop.eventually eventually_failureBound_le_exp
  apply Real.summable_exp_neg_nat.of_norm_bounded_eventually_nat
  filter_upwards [hb] with j hj
  rw [Real.norm_eq_abs, abs_of_nonneg (failureBound_nonneg (hmnonneg j))]
  exact hj.trans (Real.exp_le_exp.mpr (neg_le_neg (hm j)))

theorem summable_failureBound_of_two_pow_le {m : ℕ → ℝ}
    (hm : ∀ j, (2 : ℝ) ^ j ≤ m j) :
    Summable (fun j => failureBound (m j)) := by
  apply summable_failureBound_of_nat_le
  · intro j
    exact le_trans (by exact_mod_cast (show j < 2 ^ j from Nat.lt_two_pow_self).le) (hm j)
  · intro j
    exact le_trans (by positivity) (hm j)

theorem ae_eventually_notMem_of_phase_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (bad : ℕ → Set Ω) {m : ℕ → ℝ}
    (hm : ∀ j, (2 : ℝ) ^ j ≤ m j)
    (hbad : ∀ᶠ j in atTop, μ (bad j) ≤ ENNReal.ofReal (failureBound (m j))) :
    ∀ᵐ ω ∂μ, ∀ᶠ j in atTop, ω ∉ bad j := by
  have hs := summable_failureBound_of_two_pow_le hm
  have hreal : Summable (fun j => (μ (bad j)).toReal) := by
    apply hs.of_norm_bounded_eventually_nat
    filter_upwards [hbad] with j hj
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    have hnonneg : 0 ≤ failureBound (m j) :=
      failureBound_nonneg (le_trans (by positivity) (hm j))
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hj
    simpa only [ENNReal.toReal_ofReal hnonneg] using hh
  apply MeasureTheory.ae_eventually_notMem
  have ht := hreal.tsum_ofReal_ne_top
  simpa only [ENNReal.ofReal_toReal (measure_ne_top μ _)] using ht

end Invariant233.ProductPhases

end OAI
