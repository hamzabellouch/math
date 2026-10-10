import OAI.NumberTheory.JointDickman.Analysis.CharacterPerronBounds
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-! # Absolute integrability of the character Perron line -/
namespace JointDickman
open Complex MeasureTheory

 theorem squarefreeCharacterWeight_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (n : ℕ) :
    ‖(squarefreeWeight z n:ℂ)*χ (n:ZMod q)‖ ≤ 1 := by
  rw [norm_mul]
  apply (mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)).trans
  simpa only [Complex.norm_real, Real.norm_eq_abs] using squarefreeWeight_abs_le_one hz hz1 n

theorem characterLSeries_measurable {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℝ) :
    Measurable (LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q))) := by
  apply Measurable.tsum
  intro n
  apply Continuous.measurable
  exact continuous_iff_continuousAt.mpr (fun s => (LSeries.hasDerivAt_term _ n s).continuousAt)

theorem characterLSeries_vertical_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z σ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hσ : 1 < σ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ,
      ‖LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) ((σ:ℂ)+(t:ℂ)*I)‖ ≤ M := by
  have hs (t : ℝ) : LSeriesSummable
      (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) ((σ:ℂ)+(t:ℂ)*I) :=
    LSeriesSummable_of_bounded_of_one_lt_re
      (fun n _ => squarefreeCharacterWeight_norm_le_one χ hz hz1 n) (by simpa using hσ)
  let M := ∑' n, ‖LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q))
    ((σ:ℂ)+(0:ℂ)*I) n‖
  refine ⟨M,tsum_nonneg (fun _ => norm_nonneg _),fun t => ?_⟩
  calc
    _ ≤ ∑' n, ‖LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q))
        ((σ:ℂ)+(t:ℂ)*I) n‖ := norm_tsum_le_tsum_norm (hs t).norm
    _ = M := by
      apply tsum_congr
      intro n
      simp only [LSeries.norm_term_eq, add_re, ofReal_re, mul_re, ofReal_im,
        I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]

theorem characterNormalizedPerron_integrable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z L c : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hc : 0 < c) :
    Integrable (fun t : ℝ => characterNormalizedPerron χ z L ((c:ℂ)+(t:ℂ)*I)) := by
  obtain ⟨M,hM,hMb⟩ := characterLSeries_vertical_bound χ hz hz1 (show 1 < 1+c by linarith)
  have hm : Measurable (fun t : ℝ => characterNormalizedPerron χ z L ((c:ℂ)+(t:ℂ)*I)) := by
    unfold characterNormalizedPerron
    exact ((characterLSeries_measurable χ z).comp (by fun_prop)).mul (by fun_prop) |>.div (by fun_prop)
  have hi : Integrable (fun t : ℝ => (5*M*Real.exp (L*c))/(1+t^2)) := by
    simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul (5*M*Real.exp (L*c))
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards with t
  rw [characterNormalizedPerron_norm]
  have hseries : ‖LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q))
      (1+((c:ℂ)+(t:ℂ)*I))‖ ≤ M := by
    convert hMb t using 1
    congr 2
    push_cast
    ring
  have hden := rieszDenominator_inv_bound (s := 1+((c:ℂ)+(t:ℂ)*I)) (by simp; linarith)
  have hden' : 1/(‖1+((c:ℂ)+(t:ℂ)*I)‖*‖2+((c:ℂ)+(t:ℂ)*I)‖) ≤ 5/(1+t^2) := by
    simpa only [show (1:ℂ)+((c:ℂ)+(t:ℂ)*I)+1 = 2+((c:ℂ)+(t:ℂ)*I) by ring,
      add_im, one_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero,
      zero_add, add_zero] using hden
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
  calc
    _ ≤ (M*Real.exp (L*c))*(5/(1+t^2)) := by
      rw [div_eq_mul_inv]
      apply mul_le_mul (mul_le_mul_of_nonneg_right hseries (Real.exp_pos _).le)
        _ (by positivity) (by positivity)
      simpa only [one_div] using hden'
    _ = _ := by ring

end JointDickman

end OAI
