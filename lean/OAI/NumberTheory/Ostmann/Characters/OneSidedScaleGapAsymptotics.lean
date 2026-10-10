import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OAI

noncomputable section
namespace Ostmann.Characters
open Filter
open scoped Topology

def historyPolynomialCost (C z : ℝ) (d : ℕ) (L : ℝ) : ℝ :=
  C * (1 + (⌊z*L⌋₊ : ℝ))^d

theorem eventually_historyPolynomialCost_le (C z : ℝ) (d : ℕ) {α δ : ℝ}
    (hz : 0 ≤ z) (hα : 0 < α) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, historyPolynomialCost C z d L ≤ δ*Real.exp (α*L) := by
  have ht : Tendsto (fun L : ℝ => Real.exp (α*L)/L^d) atTop atTop := by
    simpa only [Real.rpow_natCast] using tendsto_exp_mul_div_rpow_atTop (d : ℝ) α hα
  have he := ht.eventually (eventually_ge_atTop (|C| * (z+1)^d/δ))
  filter_upwards [he,eventually_ge_atTop (1 : ℝ)] with L hE hL
  have hL0 : 0 < L := by linarith
  have hp : 0 < L^d := pow_pos hL0 _
  have hf : (⌊z*L⌋₊ : ℝ) ≤ z*L := Nat.floor_le (mul_nonneg hz hL0.le)
  have hbase : 1+(⌊z*L⌋₊ : ℝ) ≤ (z+1)*L := by nlinarith
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1+(⌊z*L⌋₊ : ℝ)) hbase d
  have hmul := mul_le_mul_of_nonneg_left ((le_div_iff₀ hp).mp hE) hδ.le
  have hcancel : δ*((|C| * (z+1)^d/δ)*L^d) = |C| * ((z+1)*L)^d := by
    rw [mul_pow]
    field_simp
  rw [hcancel] at hmul
  exact (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
    ((mul_le_mul_of_nonneg_left hpow (abs_nonneg C)).trans hmul)

theorem eventually_exp_scale_gap {β γ : ℝ} (hgap : β < γ) (A : ℝ) :
    ∀ᶠ L : ℝ in atTop, A*Real.exp (β*L) ≤ Real.exp (γ*L) := by
  have ht := Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (sub_pos.mpr hgap))
  filter_upwards [ht.eventually (eventually_ge_atTop A)] with L hL
  have hh := mul_le_mul_of_nonneg_right hL (Real.exp_pos (β*L)).le
  convert hh using 1
  simp only [Function.comp_apply,id_eq]
  rw [← Real.exp_add]
  congr 1
  ring

theorem eventually_history_scale_gap_exponents (C z : ℝ) (d : ℕ)
    {α β γ c : ℝ} (hz : 0 ≤ z) (hα : 0 < α) (hαβ : α ≤ β)
    (hβγ : β < γ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      historyPolynomialCost C z d L - c*Real.exp (α*L) ≤ -(c/2)*Real.exp (α*L) ∧
      historyPolynomialCost C z d L + 2*Real.exp (β*L) - Real.exp (γ*L) ≤ -Real.exp (α*L) := by
  filter_upwards [eventually_historyPolynomialCost_le C z d hz hα (half_pos hc),
    eventually_historyPolynomialCost_le C z d hz hα (by norm_num : (0 : ℝ)<1),
    eventually_exp_scale_gap hβγ 4,eventually_ge_atTop (0 : ℝ)] with L hpoly hpoly' hgap hL
  have he : Real.exp (α*L) ≤ Real.exp (β*L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hαβ hL)
  constructor <;> nlinarith

end Ostmann.Characters

end

end OAI
