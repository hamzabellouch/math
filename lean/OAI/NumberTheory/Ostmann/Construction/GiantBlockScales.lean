import OAI.NumberTheory.Ostmann.Construction.SelectedCellGap
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticErrorRates

namespace OAI

/-! # Specializing the initial giant block to the construction's scales -/

namespace Ostmann
open Filter

theorem eventual_giant_block_scales (a C γ c : ℝ) (hγ : 0 < γ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ lo X : ℝ,
      Real.exp ((5 / 100 : ℝ) * L) ≤ lo → lo ≤ Real.exp ((9 / 10 : ℝ) * L) →
      0 < X → X ≤ Real.exp L →
      5 ≤ lo ∧
      8 + Real.log 2 + 2 * C ≤ 10 * Real.exp ((1 / 100 : ℝ) * L) ∧
      lo + 10 * Real.exp ((1 / 100 : ℝ) * L) ≤ 2 * (lo - 4) ∧
      tailDefectBudget a C X ≤ γ ^ 2 * c ^ 2 * (10 * Real.exp ((1 / 100 : ℝ) * L)) / 512 ∧
      (∀ G : ℝ, lo - 2 ≤ G → G ≤ lo + 10 * Real.exp ((1 / 100 : ℝ) * L) + 2 →
        G ≤ (lo - 2) + 12 * Real.exp ((1 / 100 : ℝ) * L) ∧
        2 ≤ G ∧ Real.exp ((39 / 10000 : ℝ) * L) ≤ G - 1 / 2 ∧
        G ≤ Real.exp ((905 / 1000 : ℝ) * L)) := by
  let ε := γ ^ 2 * c ^ 2 * 10 / 512
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hlim : Tendsto (fun L : ℝ => tailCellLinearRate a C *
      (L / Real.exp ((1 / 100 : ℝ) * L))) atTop (nhds 0) := by
    simpa only [pow_one, mul_zero] using
      (isLittleO_pow_exp_pos_mul_atTop 1
        (by norm_num : (0 : ℝ) < 1 / 100)).tendsto_div_nhds_zero.const_mul
          (tailCellLinearRate a C)
  have hratio := hlim.eventually_le_const hε
  have hexp : Tendsto (fun L : ℝ => Real.exp ((1 / 100 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [hratio,
    arithmetic_exponent_absorption (1 / 100) (5 / 100) 0 20 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    arithmetic_exponent_absorption (39 / 10000) (5 / 100) 0 4 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    arithmetic_exponent_absorption (9 / 10) (905 / 1000) 0 12 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hexp.eventually (eventually_ge_atTop (max 2 ((8 + Real.log 2 + 2 * C) / 10))),
    eventually_ge_atTop (1 : ℝ)] with L hratio hlow hgap hupp he2 hL
  simp only [pow_one, zero_mul, Real.exp_zero] at hlow hgap hupp hratio
  have hratio' : tailCellLinearRate a C * L ≤ ε * Real.exp ((1 / 100 : ℝ) * L) := by
    rwa [← mul_div_assoc, div_le_iff₀ (Real.exp_pos _)] at hratio
  have he2' : 2 ≤ Real.exp ((1 / 100 : ℝ) * L) := (le_max_left _ _).trans he2
  have heC : (8 + Real.log 2 + 2 * C) / 10 ≤ Real.exp ((1 / 100 : ℝ) * L) :=
    (le_max_right _ _).trans he2
  have hsmallExp : Real.exp ((1 / 100 : ℝ) * L) ≤ Real.exp ((9 / 10 : ℝ) * L) :=
    Real.exp_le_exp.mpr (by nlinarith only [hL])
  have hlow' : 10 * Real.exp ((1 / 100 : ℝ) * L) + 8 ≤
      Real.exp ((5 / 100 : ℝ) * L) := by
    have h := mul_le_mul_of_nonneg_right hL (Real.exp_nonneg ((1 / 100 : ℝ) * L))
    nlinarith only [hlow, h, hL, Real.exp_nonneg ((1 / 100 : ℝ) * L)]
  have hgap' : Real.exp ((39 / 10000 : ℝ) * L) + 5 / 2 ≤
      Real.exp ((5 / 100 : ℝ) * L) := by
    have h := mul_le_mul_of_nonneg_right hL (Real.exp_nonneg ((39 / 10000 : ℝ) * L))
    nlinarith only [hgap, h, hL, Real.exp_nonneg ((39 / 10000 : ℝ) * L)]
  have hupp' : Real.exp ((9 / 10 : ℝ) * L) +
      10 * Real.exp ((1 / 100 : ℝ) * L) + 2 ≤ Real.exp ((905 / 1000 : ℝ) * L) := by
    have h := mul_le_mul_of_nonneg_right hL (Real.exp_nonneg ((9 / 10 : ℝ) * L))
    nlinarith only [hupp, h, hL, hsmallExp, Real.exp_nonneg ((9 / 10 : ℝ) * L)]
  intro lo X hlo hhi hX hXhi
  refine ⟨by nlinarith only [hlo, hlow', he2'], by linarith only [heC],
    by linarith only [hlo, hlow'], ?_, ?_⟩
  · apply (tailDefectBudget_linear a C L X hL hX hXhi).trans
    calc
      _ ≤ ε * Real.exp ((1 / 100 : ℝ) * L) := hratio'
      _ = _ := by dsimp [ε]; ring
  · intro G hGlo hGhi
    refine ⟨by linarith only [hGhi, he2'], ?_, ?_, by linarith only [hGhi, hhi, hupp']⟩
    · linarith only [hGlo, hlo, hlow', he2']
    · linarith only [hGlo, hlo, hgap']

end Ostmann

end OAI
