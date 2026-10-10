import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace OAI

namespace Invariant233.ConvolutionContradiction

theorem sqrt_exp_attenuation (L : ℝ) :
    Real.sqrt (Real.exp (-L / 400)) = Real.exp (-L / 800) := by
  rw [← Real.exp_half]
  congr 1
  ring

theorem tail_attenuation_le (L : ℝ) (hL : 0 ≤ L) :
    Real.exp (-L) + 2 * Real.sqrt (Real.exp (-L / 400)) ≤
      3 * Real.exp (-L / 10000) := by
  rw [sqrt_exp_attenuation]
  have h₁ : Real.exp (-L) ≤ Real.exp (-L / 10000) :=
    Real.exp_le_exp.mpr (by linarith)
  have h₂ : Real.exp (-L / 800) ≤ Real.exp (-L / 10000) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

theorem coefficient_tail_le (K : ℕ) (L ε j : ℝ) (hL : 0 ≤ L)
    (hchoice : (2 * (K : ℝ) + 1) * 3 * Real.exp (-L / 10000) ≤ ε / j) :
    (2 * (K : ℝ) + 1) *
      (Real.exp (-L) + 2 * Real.sqrt (Real.exp (-L / 400))) ≤ ε / j := by
  calc
    _ ≤ (2 * (K : ℝ) + 1) * (3 * Real.exp (-L / 10000)) :=
      mul_le_mul_of_nonneg_left (tail_attenuation_le L hL) (by positivity)
    _ = (2 * (K : ℝ) + 1) * 3 * Real.exp (-L / 10000) := by ring
    _ ≤ ε / j := hchoice

theorem fixed_stage_contradiction (c ε j : ℝ) (hε : 0 < ε)
    (hstage : 1 / j < c) (hbound : c * ε ≤ ε / j) : False := by
  have hstrict : ε / j < c * ε := by
    calc
      ε / j = (1 / j) * ε := by ring
      _ < c * ε := mul_lt_mul_of_pos_right hstage hε
  exact (not_lt_of_ge hbound) hstrict

theorem not_eventually_small_error (c : ℝ) (ε : ℕ → ℝ) (hc : 0 < c)
    (hε : ∀ᶠ j in Filter.atTop, 0 < ε j) :
    ¬ ∀ᶠ j in Filter.atTop, c * ε j ≤ ε j / (j : ℝ) := by
  intro hbound
  have hstage : ∀ᶠ j : ℕ in Filter.atTop, 1 / (j : ℝ) < c :=
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hc)
  obtain ⟨j, hjε, hjstage, hjbound⟩ :=
    (hε.and (hstage.and hbound)).exists
  exact fixed_stage_contradiction c (ε j) (j : ℝ) hjε hjstage hjbound

theorem not_eventually_conditional_obstruction
    (c : ℝ) (K : ℕ → ℕ) (L ε : ℕ → ℝ) (hc : 0 < c)
    (hε : ∀ᶠ j in Filter.atTop, 0 < ε j)
    (hL : ∀ᶠ j in Filter.atTop, 0 ≤ L j)
    (hchoice : ∀ᶠ j in Filter.atTop,
      (2 * (K j : ℝ) + 1) * 3 * Real.exp (-L j / 10000) ≤ ε j / (j : ℝ)) :
    ¬ ∀ᶠ j in Filter.atTop, c * ε j ≤ (2 * (K j : ℝ) + 1) *
      (Real.exp (-L j) + 2 * Real.sqrt (Real.exp (-L j / 400))) := by
  intro hbound
  apply not_eventually_small_error c ε hc hε
  filter_upwards [hL, hchoice, hbound] with j hjL hjchoice hjbound
  exact hjbound.trans (coefficient_tail_le (K j) (L j) (ε j) (j : ℝ) hjL hjchoice)

end Invariant233.ConvolutionContradiction

end OAI
