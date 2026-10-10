import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.ScaleBudget
open Filter Asymptotics
open scoped Topology

structure Row where
  a₀ : ℝ
  a₁ : ℝ
  μ : ℝ
  δ : ℝ
  δ' : ℝ
  θ : ℝ
  target : ℝ
  μ_pos : 0 < μ
  μ_lt_δ : μ < δ
  δ_lt_δ' : δ < δ'
  δ'_lt_θ : δ' < θ
  zero_gap : 3*θ < a₀
  range : a₀ < a₁
  target_pos : 0 < target
  target_lt_δ : target < δ

def giant : Row where
  a₀ := 49/1000
  a₁ := 95/100
  μ := 12/1000
  δ := 14/1000
  δ' := 15/1000
  θ := 16/1000
  target := 13/1000
  μ_pos := by norm_num
  μ_lt_δ := by norm_num
  δ_lt_δ' := by norm_num
  δ'_lt_θ := by norm_num
  zero_gap := by norm_num
  range := by norm_num
  target_pos := by norm_num
  target_lt_δ := by norm_num

def bulk : Row where
  a₀ := 39/10000
  a₁ := 7/1000
  μ := 11/10000
  δ := 115/100000
  δ' := 12/10000
  θ := 125/100000
  target := 11/10000
  μ_pos := by norm_num
  μ_lt_δ := by norm_num
  δ_lt_δ' := by norm_num
  δ'_lt_θ := by norm_num
  zero_gap := by norm_num
  range := by norm_num
  target_pos := by norm_num
  target_lt_δ := by norm_num

theorem bulk_spectator_gap : (1:ℝ)/1000 < bulk.μ := by norm_num [bulk]
theorem giant_conclusion_gap : (12:ℝ)/1000 < giant.δ' := by norm_num [giant]

theorem eventually_poly_exp_le (C : ℝ) (n : ℕ) {a b K : ℝ}
    (hab : a < b) (hK : 0 < K) :
    ∀ᶠ L : ℝ in atTop, C * L^n * Real.exp (a*L) ≤ K * Real.exp (b*L) := by
  have h : (fun L : ℝ => C * (Real.exp (a*L) * L^n)) =o[atTop]
      (fun L : ℝ => Real.exp (b*L)) := by
    have h₀ := isLittleO_exp_mul_rpow_of_lt (n:ℝ) hab
    simp only [Real.rpow_natCast] at h₀
    exact h₀.const_mul_left C
  filter_upwards [h.bound hK] with L hL
  calc
    C*L^n*Real.exp (a*L) = C*(Real.exp (a*L)*L^n) := by ring
    _ ≤ ‖C*(Real.exp (a*L)*L^n)‖ := le_abs_self _
    _ ≤ K*Real.exp (b*L) := by simpa only [Real.norm_eq_abs,
      Real.abs_exp] using hL

theorem eventually_double_exp_error (C : ℝ) (n : ℕ) {a b d c : ℝ}
    (hab : a < b) (hdb : d < b) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (-c*Real.exp (b*L)+C*L^n*Real.exp (a*L)) ≤
        Real.exp (-Real.exp (d*L)) := by
  have hhalf : 0 < c/2 := by linarith
  filter_upwards [eventually_poly_exp_le C n hab hhalf,
    eventually_poly_exp_le 1 0 hdb hhalf] with L h₁ h₂
  apply Real.exp_le_exp.mpr
  simp only [pow_zero, mul_one, one_mul] at h₂
  linarith

end Ostmann.Arithmetic.ScaleBudget

end

end OAI
