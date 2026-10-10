import OAI.NumberTheory.JointDickman.Counting.UnitProgressionBinShort

namespace OAI

/-! # Linear and quadratic estimates for unit-progression bin averages -/
namespace JointDickman
open Finset Filter MeasureTheory Classical

theorem unitProgressionBinAverage_sub {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (u v : ArithmeticFunction ℝ)
    {q : ℕ} (r : (ZMod q)ˣ) (H z : ℝ) :
    unitProgressionBinAverage E ζ μ u r H z-unitProgressionBinAverage E ζ μ v r H z =
      unitProgressionBinAverage E ζ μ (u-v) r H z := by
  unfold unitProgressionBinAverage
  rw [← sub_div,← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro n _
  simp only [sub_eq_add_neg,ArithmeticFunction.add_apply,ArithmeticFunction.neg_apply,Complex.ofReal_add,Complex.ofReal_neg]
  split_ifs <;> ring

theorem unitProgressionBinAverage_energy_triangle {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (u v : ArithmeticFunction ℝ)
    {q : ℕ} (r : (ZMod q)ˣ) {H X : ℝ} (hH : 0 < H) (hX : 0 < X) :
    (1/X)*(∫ z in X..2*X, ‖unitProgressionBinAverage E ζ μ u r H z‖^2) ≤
      2*((1/X)*(∫ z in X..2*X,
        ‖unitProgressionBinAverage E ζ μ u r H z-unitProgressionBinAverage E ζ μ v r H z‖^2))+
      2*((1/X)*(∫ z in X..2*X, ‖unitProgressionBinAverage E ζ μ v r H z‖^2)) := by
  have hdiff : IntervalIntegrable (fun z =>
      ‖unitProgressionBinAverage E ζ μ u r H z-unitProgressionBinAverage E ζ μ v r H z‖^2)
      volume X (2*X) := by
    simp_rw [unitProgressionBinAverage_sub]
    exact unitProgressionBinAverage_sq_integrable E ζ μ (u-v) r hH _ _
  have hv := unitProgressionBinAverage_sq_integrable E ζ μ v r hH X (2*X)
  have hu := unitProgressionBinAverage_sq_integrable E ζ μ u r hH X (2*X)
  have hp z : ‖unitProgressionBinAverage E ζ μ u r H z‖^2 ≤
      2*‖unitProgressionBinAverage E ζ μ u r H z-unitProgressionBinAverage E ζ μ v r H z‖^2+
      2*‖unitProgressionBinAverage E ζ μ v r H z‖^2 := by
    let a := unitProgressionBinAverage E ζ μ u r H z
    let b := unitProgressionBinAverage E ζ μ v r H z
    have hh : ‖a‖ ≤ ‖a-b‖+‖b‖ := by simpa only [sub_add_cancel] using norm_add_le (a-b) b
    have hs := pow_le_pow_left₀ (norm_nonneg _) hh 2
    nlinarith [sq_nonneg (‖a-b‖-‖b‖)]
  have he := intervalIntegral.integral_mono (by linarith : X ≤ 2*X) hu
    ((hdiff.const_mul 2).add (hv.const_mul 2)) hp
  rw [intervalIntegral.integral_add (hdiff.const_mul 2) (hv.const_mul 2),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at he
  convert mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 1/X) using 1
  ring

end JointDickman

end OAI
