import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.ZeroDensity.FiniteDecay

namespace OAI

open Filter
open scoped Topology

namespace Ostmann.ZeroDensity

theorem eventually_linear_mul_exp_le {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, C * L * Real.exp (a * L) ≤ Real.exp (b * L) := by
  have hlim : Tendsto (fun L : ℝ => Real.exp ((b - a) * L) / L) atTop atTop := by
    simpa only [Real.rpow_one] using
      tendsto_exp_mul_div_rpow_atTop (1 : ℝ) (b - a) (sub_pos.mpr hab)
  filter_upwards [(tendsto_atTop.1 hlim) C, eventually_gt_atTop (0 : ℝ)] with L h hL
  have hc : C * L ≤ Real.exp ((b - a) * L) := (le_div_iff₀ hL).mp h
  calc
    C * L * Real.exp (a * L) ≤ Real.exp ((b - a) * L) * Real.exp (a * L) := by
      gcongr
    _ = Real.exp (b * L) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem eventually_supply_density_exponent (CK : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ K : ℝ, K ≤ CK * L →
      2 * (42 * K * Real.exp (9 * L / 10)) ≤ Real.exp L := by
  have h := eventually_linear_mul_exp_le (a := (9 : ℝ) / 10) (b := 1)
    (by norm_num) (84 * CK)
  filter_upwards [h] with L h K hK
  have he := Real.exp_pos (9 * L / 10)
  have hmul := mul_le_mul_of_nonneg_right hK he.le
  have heq : 9 / 10 * L = 9 * L / 10 := by ring
  rw [heq, one_mul] at h
  nlinarith

theorem supply_gap_gain {c CK K L : ℝ} (hc : 0 < c) (_hCK : 0 < CK)
    (hK : 0 < K) (_hL : 0 < L) (hKL : K ≤ CK * L) :
    (c / (24 * CK)) * Real.exp (L / 10) / L ≤
      Real.exp L * (c / (12 * K * Real.exp (9 * L / 10))) / 2 := by
  have he : Real.exp L = Real.exp (L / 10) * Real.exp (9 * L / 10) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    c / (24 * CK) * Real.exp (L / 10) / L =
        c * Real.exp (L / 10) / (24 * CK * L) := by ring
    _ ≤ c * Real.exp (L / 10) / (24 * K) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    _ = Real.exp L * (c / (12 * K * Real.exp (9 * L / 10))) / 2 := by
      rw [he]
      field_simp
      ring

theorem eventually_prefactor_decay {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (C D : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      (Real.exp L + 1) * Real.exp (C * L) *
          Real.exp (1 - c * Real.exp (a * L) / L) ≤ Real.exp (-D * L) := by
  have hlim : Tendsto (fun L : ℝ => c * Real.exp (a * L) / L ^ 2) atTop atTop := by
    simpa only [Real.rpow_two, mul_div_assoc] using
      (tendsto_exp_mul_div_rpow_atTop (2 : ℝ) a ha).const_mul_atTop hc
  filter_upwards [(tendsto_atTop.1 hlim) (C + D + 3), eventually_ge_atTop (1 : ℝ)]
    with L hlarge hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hlarge' : (C + D + 3) * L ^ 2 ≤ c * Real.exp (a * L) :=
    (le_div_iff₀ (sq_pos_of_pos hLpos)).mp hlarge
  have hlinear : (C + D + 3) * L ≤ c * Real.exp (a * L) / L := by
    apply (le_div_iff₀ hLpos).mpr
    nlinarith only [hlarge']
  have hexp : 2 ≤ Real.exp L := by
    have := Real.add_one_le_exp L
    linarith
  have hfactor : Real.exp L + 1 ≤ Real.exp (2 * L) := by
    rw [show 2 * L = L + L by ring, Real.exp_add]
    nlinarith
  calc
    (Real.exp L + 1) * Real.exp (C * L) *
        Real.exp (1 - c * Real.exp (a * L) / L) ≤
      Real.exp (2 * L) * Real.exp (C * L) *
        Real.exp (1 - c * Real.exp (a * L) / L) := by gcongr
    _ = Real.exp ((2 + C) * L + 1 - c * Real.exp (a * L) / L) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-D * L) := by
      apply Real.exp_le_exp.mpr
      linarith

theorem eventually_supply_prefactor_decay {c : ℝ} (hc : 0 < c) (C D : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      (Real.exp L + 1) * Real.exp (C * L) *
          Real.exp (1 - c * Real.exp (L / 10) / L) ≤ Real.exp (-D * L) := by
  simpa only [one_div_mul_eq_div] using
    eventually_prefactor_decay (a := (1 : ℝ) / 10) (by norm_num) hc C D

end Ostmann.ZeroDensity

end OAI
