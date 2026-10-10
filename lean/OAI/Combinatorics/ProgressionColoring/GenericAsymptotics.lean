import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Growth comparisons for the absolute parameter threshold

These comparisons concern only the progression length and fixed real constants.
They contain no color-count parameter and can therefore be combined before the
digit-product transfer to choose one absolute threshold.
-/

noncomputable section

open Filter Topology

namespace QuantitativeVanDerWaerden.Scaling

/-- A fixed power times a logarithm is eventually bounded by any prescribed
positive multiple of a strictly larger power. -/
theorem eventually_rpow_log_le_real {a b C eps : ℝ}
    (hab : a < b) (hC : 0 ≤ C) (he : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a * Real.log x ≤ eps * x ^ b := by
  have hC1 : 0 < C + 1 := by linarith
  have hlog : ∀ᶠ x : ℝ in atTop,
      ‖Real.log x‖ ≤ (eps / (C + 1)) * ‖x ^ (b - a)‖ :=
    (isLittleO_log_rpow_atTop (sub_pos.mpr hab)).bound (div_pos he hC1)
  filter_upwards [hlog, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hxpos : 0 < x := zero_lt_one.trans_le hx1
  have hpow : 0 ≤ x ^ a := Real.rpow_nonneg hxpos.le _
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_of_nonneg hlog0,
    Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le _)] at hx
  calc
    C * x ^ a * Real.log x ≤ (C + 1) * x ^ a * Real.log x :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1) hpow) hlog0
    _ ≤ (C + 1) * x ^ a * ((eps / (C + 1)) * x ^ (b - a)) :=
      mul_le_mul_of_nonneg_left hx (mul_nonneg hC1.le hpow)
    _ = eps * (x ^ a * x ^ (b - a)) := by
      field_simp [hC1.ne']
    _ = eps * x ^ b := by
      rw [← Real.rpow_add hxpos, show a + (b - a) = b by ring]

/-- Natural-input version of the power-logarithm comparison. -/
theorem eventually_rpow_log_le {a b C eps : ℝ}
    (hab : a < b) (hC : 0 ≤ C) (he : 0 < eps) :
    ∀ᶠ k : ℕ in atTop,
      C * (k : ℝ) ^ a * Real.log k ≤ eps * (k : ℝ) ^ b :=
  (eventually_rpow_log_le_real hab hC he).natCast_atTop

/-- A fixed multiple of a power is eventually smaller than a prescribed
positive multiple of any strictly larger power. -/
theorem eventually_rpow_le_real {a b C eps : ℝ}
    (hab : a < b) (_hC : 0 ≤ C) (he : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a ≤ eps * x ^ b := by
  have hlarge : ∀ᶠ x : ℝ in atTop, C / eps ≤ x ^ (b - a) :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop (C / eps)
  filter_upwards [hlarge, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  calc
    C * x ^ a = (eps * x ^ a) * (C / eps) := by
      field_simp [he.ne']
    _ ≤ (eps * x ^ a) * x ^ (b - a) :=
      mul_le_mul_of_nonneg_left hx (mul_nonneg he.le (Real.rpow_nonneg hxpos.le _))
    _ = eps * (x ^ a * x ^ (b - a)) := by ring
    _ = eps * x ^ b := by
      rw [← Real.rpow_add hxpos, show a + (b - a) = b by ring]

/-- Natural-input version of the power comparison. -/
theorem eventually_rpow_le {a b C eps : ℝ}
    (hab : a < b) (hC : 0 ≤ C) (he : 0 < eps) :
    ∀ᶠ k : ℕ in atTop, C * (k : ℝ) ^ a ≤ eps * (k : ℝ) ^ b :=
  (eventually_rpow_le_real hab hC he).natCast_atTop

/-- Every positive real power of natural numbers tends to infinity. -/
theorem tendsto_nat_rpow_atTop {t : ℝ} (ht : 0 < t) :
    Tendsto (fun k : ℕ => (k : ℝ) ^ t) atTop atTop :=
  (tendsto_rpow_atTop ht).comp tendsto_natCast_atTop_atTop

/-- An arbitrary fixed lower threshold is eventually crossed by a positive
real power of natural numbers. -/
theorem eventually_le_nat_rpow {t : ℝ} (ht : 0 < t) (L : ℝ) :
    ∀ᶠ k : ℕ in atTop, L ≤ (k : ℝ) ^ t :=
  (tendsto_nat_rpow_atTop ht).eventually_ge_atTop L

/-- Negative powers of natural numbers tend to zero. -/
theorem tendsto_nat_rpow_neg_zero {t : ℝ} (ht : 0 < t) :
    Tendsto (fun k : ℕ => (k : ℝ) ^ (-t)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop ht).comp tendsto_natCast_atTop_atTop

/-- A positive power in the negative exponent dominates any lower power
times a logarithm. The hypothesis `0 < t` is needed for decay to zero. -/
theorem tendsto_exp_rpow_log_sub_rpow_real {a t C b : ℝ}
    (hat : a < t) (hC : 0 ≤ C) (hb : 0 < b) (ht : 0 < t) :
    Tendsto (fun x : ℝ => Real.exp (C * x ^ a * Real.log x - b * x ^ t))
      atTop (𝓝 0) := by
  have hbound : ∀ᶠ x : ℝ in atTop,
      C * x ^ a * Real.log x ≤ (b / 2) * x ^ t :=
    eventually_rpow_log_le_real hat hC (by linarith)
  have hneg : Tendsto (fun x : ℝ => (-(b / 2)) * x ^ t) atTop atBot :=
    (tendsto_rpow_atTop ht).const_mul_atTop_of_neg (by linarith)
  apply Real.tendsto_exp_atBot.comp
  apply tendsto_atBot_mono' atTop _ hneg
  filter_upwards [hbound] with x hx
  nlinarith

/-- Natural-input exponential decay, used in both perturbation union bounds. -/
theorem tendsto_exp_rpow_log_sub_rpow {a t C b : ℝ}
    (hat : a < t) (hC : 0 ≤ C) (hb : 0 < b) (ht : 0 < t) :
    Tendsto (fun k : ℕ =>
      Real.exp (C * (k : ℝ) ^ a * Real.log k - b * (k : ℝ) ^ t))
      atTop (𝓝 0) := by
  simpa only [Function.comp_def] using
    (tendsto_exp_rpow_log_sub_rpow_real hat hC hb ht).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop)

/-- An exponential of a negative positive power dominates every polynomial
prefactor, including the finite number of local pattern lengths. -/
theorem tendsto_rpow_mul_exp_neg_rpow {a b t : ℝ}
    (hb : 0 < b) (ht : 0 < t) :
    Tendsto (fun k : ℕ =>
      (k : ℝ) ^ a * Real.exp (-b * (k : ℝ) ^ t)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a / t) b hb).comp
    (tendsto_nat_rpow_atTop ht)
  convert h using 1
  funext k
  dsimp only [Function.comp_def]
  rw [← Real.rpow_mul (Nat.cast_nonneg k),
    show t * (a / t) = a by field_simp [ht.ne']]

end QuantitativeVanDerWaerden.Scaling

end

end OAI
