import OAI.Combinatorics.ProgressionColoring.Parameters
import OAI.Combinatorics.ProgressionColoring.GenericAsymptotics
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Lean.Elab.Tactic.Omega

namespace OAI

/-!
# Decay of the local anchored-pattern union bound

The constants in this estimate are fixed independently of the progression length
and of the number of colors.  The sum is finite: its upper endpoint is twice the
cutoff of the construction.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace QuantitativeVanDerWaerden.Parameters

/-- The local union-bound sum, allowing any fixed nonnegative dimension
coefficient in the pattern count. -/
def localTail (C a : ℝ) (k : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc (dimension k ^ 2 + 1) (2 * cutoff k),
    (C * (dimension k : ℝ) * h) ^ (a * dimension k) *
      Real.exp (-(h : ℝ) / 64)

theorem localTail_nonneg (C a : ℝ) (hC : 0 ≤ C) (k : ℕ) :
    0 ≤ localTail C a k := by
  apply Finset.sum_nonneg
  intro h _
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _)

/-- The logarithm of every local counting base has the same bound on the
finite interval of lengths. -/
theorem local_count_log_le {C : ℝ} (hC : 1 ≤ C) {k h : ℕ}
    (hk : 1 ≤ k) (hlog : 1 ≤ Real.log k)
    (hh : h ∈ Finset.Icc (dimension k ^ 2 + 1) (2 * cutoff k)) :
    Real.log (C * (dimension k : ℝ) * h) ≤
      (Real.log (8 * C) + 1) * Real.log k := by
  have hCpos : 0 < C := by linarith
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hDpos : (0 : ℝ) < dimension k := Nat.cast_pos.mpr (dimension_pos hk)
  have hh' := Finset.mem_Icc.mp hh
  have hhpos : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  have hhupper : (h : ℝ) ≤ 2 * cutoff k := by exact_mod_cast hh'.2
  have hbase : 0 < C * (dimension k : ℝ) * h := by positivity
  have hbaseupper : C * (dimension k : ℝ) * h ≤
      (8 * C) * (k : ℝ) ^ (3 / 5 : ℝ) := by
    calc
      C * (dimension k : ℝ) * h ≤ C * dimension k * (2 * cutoff k) :=
        mul_le_mul_of_nonneg_left hhupper (by positivity)
      _ = (2 * C) * ((dimension k : ℝ) * cutoff k) := by ring
      _ ≤ (2 * C) * (4 * (k : ℝ) ^ (3 / 5 : ℝ)) :=
        mul_le_mul_of_nonneg_left (dimension_cutoff_upper hk) (by positivity)
      _ = (8 * C) * (k : ℝ) ^ (3 / 5 : ℝ) := by ring
  have hlogC : 0 ≤ Real.log (8 * C) := Real.log_nonneg (by linarith)
  have hlogk : 0 ≤ Real.log k := by linarith
  calc
    Real.log (C * (dimension k : ℝ) * h) ≤
        Real.log ((8 * C) * (k : ℝ) ^ (3 / 5 : ℝ)) :=
      Real.log_le_log hbase hbaseupper
    _ = Real.log (8 * C) + (3 / 5 : ℝ) * Real.log k := by
      rw [Real.log_mul (by positivity : 8 * C ≠ 0)
        (Real.rpow_pos_of_pos hkpos _).ne', Real.log_rpow hkpos]
    _ ≤ (Real.log (8 * C) + 1) * Real.log k := by
      nlinarith [mul_nonneg hlogC (sub_nonneg.mpr hlog)]

/-- A finite envelope from one numerical power-logarithm comparison. -/
theorem localTail_le_of_power_log_le {C a : ℝ} (hC : 1 ≤ C) (ha : 0 ≤ a)
    {k : ℕ} (hk : 1 ≤ k) (hlog : 1 ≤ Real.log k)
    (hsmall : (2 * a * (Real.log (8 * C) + 1)) *
      (k : ℝ) ^ (1 / 10 : ℝ) * Real.log k ≤
        (1 / 128 : ℝ) * (k : ℝ) ^ (1 / 5 : ℝ)) :
    localTail C a k ≤ 4 * (k : ℝ) ^ (1 / 2 : ℝ) *
      Real.exp (-(k : ℝ) ^ (1 / 5 : ℝ) / 128) := by
  have hCpos : 0 < C := by linarith
  have hlogC : 0 ≤ Real.log (8 * C) := Real.log_nonneg (by linarith)
  have hA : 0 ≤ Real.log (8 * C) + 1 := by linarith
  have hlogk : 0 ≤ Real.log k := by linarith
  have hterm : ∀ h ∈ Finset.Icc (dimension k ^ 2 + 1) (2 * cutoff k),
      (C * (dimension k : ℝ) * h) ^ (a * dimension k) *
        Real.exp (-(h : ℝ) / 64) ≤
          Real.exp (-(k : ℝ) ^ (1 / 5 : ℝ) / 128) := by
    intro h hh
    have hh' := Finset.mem_Icc.mp hh
    have hDpos : (0 : ℝ) < dimension k := Nat.cast_pos.mpr (dimension_pos hk)
    have hhpos : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
    have hbase : 0 < C * (dimension k : ℝ) * h := by positivity
    have hhD : (dimension k : ℝ) ^ 2 ≤ h := by
      exact_mod_cast (show dimension k ^ 2 ≤ h by omega)
    have hhpower : (k : ℝ) ^ (1 / 5 : ℝ) ≤ h :=
      (dimension_sq_lower k).trans hhD
    have hcount : a * dimension k * Real.log (C * (dimension k : ℝ) * h) ≤
        (1 / 128 : ℝ) * (k : ℝ) ^ (1 / 5 : ℝ) := by
      calc
        a * dimension k * Real.log (C * (dimension k : ℝ) * h) ≤
            (a * dimension k) * ((Real.log (8 * C) + 1) * Real.log k) :=
          mul_le_mul_of_nonneg_left (local_count_log_le hC hk hlog hh) (by positivity)
        _ ≤ (a * (2 * (k : ℝ) ^ (1 / 10 : ℝ))) *
            ((Real.log (8 * C) + 1) * Real.log k) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (dimension_upper hk) ha)
            (mul_nonneg hA hlogk)
        _ = (2 * a * (Real.log (8 * C) + 1)) *
            (k : ℝ) ^ (1 / 10 : ℝ) * Real.log k := by ring
        _ ≤ _ := hsmall
    rw [Real.rpow_def_of_pos hbase, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hcard : (Finset.Icc (dimension k ^ 2 + 1) (2 * cutoff k)).card ≤
      2 * cutoff k := by
    rw [Nat.card_Icc]
    omega
  have hcardreal :
      ((Finset.Icc (dimension k ^ 2 + 1) (2 * cutoff k)).card : ℝ) ≤
        4 * (k : ℝ) ^ (1 / 2 : ℝ) := by
    have hcard' :
        ((Finset.Icc (dimension k ^ 2 + 1) (2 * cutoff k)).card : ℝ) ≤
          2 * cutoff k := by exact_mod_cast hcard
    have := cutoff_upper hk
    linarith
  calc
    localTail C a k ≤ ∑ _h ∈ Finset.Icc (dimension k ^ 2 + 1) (2 * cutoff k),
        Real.exp (-(k : ℝ) ^ (1 / 5 : ℝ) / 128) := Finset.sum_le_sum hterm
    _ = ((Finset.Icc (dimension k ^ 2 + 1) (2 * cutoff k)).card : ℝ) *
        Real.exp (-(k : ℝ) ^ (1 / 5 : ℝ) / 128) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcardreal (Real.exp_nonneg _)

/-- The local union-bound sum has an eventual bound independent of the number
of colors. -/
theorem eventually_localTail_le {C a : ℝ} (hC : 1 ≤ C) (ha : 0 ≤ a) :
    ∀ᶠ k : ℕ in atTop, localTail C a k ≤
      4 * (k : ℝ) ^ (1 / 2 : ℝ) *
        Real.exp (-(k : ℝ) ^ (1 / 5 : ℝ) / 128) := by
  have hlogC : 0 ≤ Real.log (8 * C) := Real.log_nonneg (by linarith)
  have hcoef : 0 ≤ 2 * a * (Real.log (8 * C) + 1) := by positivity
  have hsmall := Scaling.eventually_rpow_log_le
    (a := (1 / 10 : ℝ)) (b := (1 / 5 : ℝ))
    (C := 2 * a * (Real.log (8 * C) + 1)) (eps := (1 / 128 : ℝ))
    (by norm_num) hcoef (by norm_num)
  have hlog : ∀ᶠ k : ℕ in atTop, 1 ≤ Real.log k :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hsmall, hlog, eventually_ge_atTop (1 : ℕ)] with k hs hl hk
  exact localTail_le_of_power_log_le hC ha hk hl hs

/-- The entire finite local-pattern error tends to zero. -/
theorem tendsto_localTail_zero {C a : ℝ} (hC : 1 ≤ C) (ha : 0 ≤ a) :
    Tendsto (localTail C a) atTop (𝓝 0) := by
  have hdecay := Scaling.tendsto_rpow_mul_exp_neg_rpow
    (a := (1 / 2 : ℝ)) (b := (1 / 128 : ℝ)) (t := (1 / 5 : ℝ))
    (by norm_num) (by norm_num)
  have hbound : Tendsto (fun k : ℕ =>
      4 * (k : ℝ) ^ (1 / 2 : ℝ) *
        Real.exp (-(k : ℝ) ^ (1 / 5 : ℝ) / 128)) atTop (𝓝 0) := by
    have he (x : ℝ) : -(1 / 128 : ℝ) * x = -x / 128 := by ring
    simpa only [he, mul_zero, mul_assoc] using hdecay.const_mul (4 : ℝ)
  exact squeeze_zero' (Eventually.of_forall (localTail_nonneg C a (by linarith)))
    (eventually_localTail_le hC ha) hbound

end QuantitativeVanDerWaerden.Parameters

end

end OAI
