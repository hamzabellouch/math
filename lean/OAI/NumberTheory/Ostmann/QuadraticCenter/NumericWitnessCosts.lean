import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterCostBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

theorem eventually_auxiliary_exp_cost (C A epsilon : ℝ) (_hC : 0 ≤ C)
    (hA : 0 ≤ A) (hepsilon : 0 < epsilon) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      1 ≤ Z → T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z →
      Real.log z ≤ 2*T^auxiliaryExponent →
      C*Real.exp (A*(auxiliaryK Z z:ℝ)) ≤ (Z:ℝ)^epsilon := by
  have hsmall := eventually_auxiliaryK_le_log (epsilon/(2*(A+1))) (by positivity)
  filter_upwards [hsmall,eventually_ge_atTop (4*C/epsilon)] with T hK hT
  intro Z z hZ hZl hZu hz hzl hzu
  have hZp : (0:ℝ) < Z := by exact_mod_cast hZ
  have hK0 : (0:ℝ) ≤ auxiliaryK Z z := Nat.cast_nonneg _
  have hk := hK Z z hZl hZu hz hzl hzu
  have hka := mul_le_mul_of_nonneg_left hk (show 0 ≤ A+1 by linarith)
  have he : (A+1)*(epsilon/(2*(A+1))*Real.log Z) = epsilon/2*Real.log Z := by
    field_simp
  rw [he] at hka
  have ha : A*(auxiliaryK Z z:ℝ) ≤ epsilon/2*Real.log Z := by nlinarith
  have ht := (div_le_iff₀ hepsilon).mp hT
  have hc : C ≤ epsilon/2*Real.log Z := by nlinarith
  calc
    C*Real.exp (A*(auxiliaryK Z z:ℝ)) ≤
        Real.exp C*Real.exp (A*(auxiliaryK Z z:ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp C]) (Real.exp_pos _).le
    _ = Real.exp (C+A*(auxiliaryK Z z:ℝ)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (Real.log Z*epsilon) := Real.exp_le_exp.mpr (by nlinarith)
    _ = (Z:ℝ)^epsilon := (Real.rpow_def_of_pos hZp epsilon).symm

theorem eventually_auxiliary_exp_dominates_log (C : ℝ) (_hC : 0 < C) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z →
      Real.log z ≤ 2*T^auxiliaryExponent → ∀ Y : ℝ,
      0 < Y → Real.log Y ≤ 7*Real.log Z →
      1024*(1+Real.log (2*Y))*(10*C)^2 ≤ Real.exp (6*(auxiliaryK Z z:ℝ)) := by
  have hpower := eventually_mul_rpow_le_rpow (16384*(10*C)^2/18)
    (a := 1) (b := 3/2) (by norm_num)
  filter_upwards [eventually_auxiliaryK_bounds,hpower,eventually_ge_atTop (1:ℝ)]
    with T hK hp hT
  intro Z z hZl hZu hz hzl hzu Y hY hlogY
  have hk := (hK Z z hZl hZu hz hzl hzu).1
  have hT0 : 0 < T := by linarith
  have hk0 : (0:ℝ) ≤ auxiliaryK Z z := Nat.cast_nonneg _
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hlog : 1+Real.log (2*Y) ≤ 16*T := by
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hY.ne']
    linarith
  have hpow : T^(3/2:ℝ) ≤ (auxiliaryK Z z:ℝ)^2 := by
    have hh : T^(3/2:ℝ) = (T^(3/4:ℝ))^2 := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hT0.le]
      norm_num
    rw [hh]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hT0.le _) hk 2
  have he := Real.sum_le_exp_of_nonneg
    (show 0 ≤ 6*(auxiliaryK Z z:ℝ) by positivity) 3
  norm_num [Finset.sum_range_succ,Nat.factorial] at he
  have hexp : 18*(auxiliaryK Z z:ℝ)^2 ≤ Real.exp (6*(auxiliaryK Z z:ℝ)) := by nlinarith
  rw [Real.rpow_one] at hp
  have hmain := mul_le_mul_of_nonneg_right hlog (sq_nonneg (10*C))
  nlinarith

end Ostmann.QuadraticCenter

end

end OAI
