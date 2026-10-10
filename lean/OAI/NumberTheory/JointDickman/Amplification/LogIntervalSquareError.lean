import OAI.NumberTheory.JointDickman.Amplification.LogIntervalApproximation

namespace OAI

/-! # Explicit squared-error bound for polynomial log-interval tests -/
namespace JointDickman
open Finset Classical

theorem polynomial_log_interval_square_error {a b δ η D : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ)
    (P : Polynomial ℝ)
    (hP : ∀ t ∈ Set.Icc (0 : ℝ) 1, |P.eval t-logIntervalRamp a b δ t/D| ≤ η)
    {s : ℝ} (hs : 0 ≤ s) :
    ((if s ∈ Set.Ioc a b then (1 : ℝ)/D else 0)-P.eval (Real.exp (-s)))^2 ≤
      2/D^2*((if s ∈ Set.Ioc (a-δ) a then (1 : ℝ) else 0)+
        (if s ∈ Set.Ioc b (b+δ) then (1 : ℝ) else 0))+2*η^2 := by
  let r := logIntervalRamp a b δ (Real.exp (-s))
  let t := if s ∈ Set.Ioc a b then (1 : ℝ) else 0
  have he := logIntervalRamp_square_error hab hδ s
  change (t-r)^2 ≤ _ at he
  have hp := hP (Real.exp (-s)) ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (by linarith)⟩
  have hp' : (r/D-P.eval (Real.exp (-s)))^2 ≤ η^2 := by
    rcases abs_le.mp hp with ⟨hl,hu⟩
    change -η ≤ P.eval (Real.exp (-s))-r/D at hl
    change P.eval (Real.exp (-s))-r/D ≤ η at hu
    nlinarith [sq_nonneg (P.eval (Real.exp (-s))-r/D)]
  have he' := div_le_div_of_nonneg_right he (sq_nonneg D)
  have hsplit : (t/D-P.eval (Real.exp (-s)))^2 ≤
      2*((t-r)/D)^2+2*(r/D-P.eval (Real.exp (-s)))^2 := by
    rw [sub_div]
    nlinarith [sq_nonneg ((t/D-r/D)-(r/D-P.eval (Real.exp (-s))))]
  have ht : (if s ∈ Set.Ioc a b then (1 : ℝ)/D else 0) = t/D := by
    dsimp [t]
    split_ifs <;> simp
  rw [ht]
  rw [div_pow] at hsplit
  calc
    _ ≤ 2*(((if s ∈ Set.Ioc (a-δ) a then (1 : ℝ) else 0)+
        (if s ∈ Set.Ioc b (b+δ) then (1 : ℝ) else 0))/D^2)+2*η^2 :=
      hsplit.trans (add_le_add (mul_le_mul_of_nonneg_left he' (by norm_num))
        (mul_le_mul_of_nonneg_left hp' (by norm_num)))
    _ = _ := by ring

end JointDickman

end OAI
