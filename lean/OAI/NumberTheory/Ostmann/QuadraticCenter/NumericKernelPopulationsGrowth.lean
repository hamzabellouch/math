import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterSelection

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

private theorem numericKernel_tail_powers {X η : ℝ} (hX : 0 < X) :
    X^(η/10)*(4*Real.sqrt (X/X^η)+8*Real.sqrt (X^(η/10))) =
      4*X^(1/2-2*η/5)+8*X^(3*η/20) := by
  have hfirst : Real.sqrt (X/X^η) = X^(1/2-η/2) := by
    have he : X/X^η = X^(1-η) := by rw [Real.rpow_sub hX, Real.rpow_one]
    rw [he, Real.sqrt_eq_rpow, ←Real.rpow_mul hX.le]
    congr 1
    ring
  have hsecond : Real.sqrt (X^(η/10)) = X^(η/20) := by
    rw [Real.sqrt_eq_rpow, ←Real.rpow_mul hX.le]
    congr 1
    ring
  rw [hfirst,hsecond,mul_add]
  have ha : X^(η/10)*X^(1/2-η/2) = X^(1/2-2*η/5) := by
    rw [←Real.rpow_add hX]
    congr 1
    ring
  have hb : X^(η/10)*X^(η/20) = X^(3*η/20) := by
    rw [←Real.rpow_add hX]
    congr 1
    ring
  calc
    _ = 4*(X^(η/10)*X^(1/2-η/2))+8*(X^(η/10)*X^(η/20)) := by ring
    _ = _ := by rw [ha,hb]

theorem eventually_numericKernel_population_budget (c η : ℝ)
    (hc : 0 < c) (hη : 0 < η) (hηu : η ≤ 1/10) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧ 0 < Real.log X ∧
      X^(η/10)*(4*Real.sqrt (X/X^η)+8*Real.sqrt (X^(η/10)))+
        X^(η/10)*X^(1/2-3*η) ≤ c*Real.sqrt X/(Real.log X)^3 := by
  have hl := (isLittleO_log_rpow_rpow_atTop 3 (by linarith : 0 < η/10)).bound hc
  filter_upwards [hl, eventually_ge_atTop (2 : ℝ),
    eventually_mul_rpow_le_rpow 12 (a := 1/2-2*η/5) (b := 1/2-η/10) (by linarith),
    eventually_mul_rpow_le_rpow 24 (a := 3*η/20) (b := 1/2-η/10) (by linarith),
    eventually_mul_rpow_le_rpow 3 (a := 1/2-29*η/10) (b := 1/2-η/10) (by linarith)]
    with X hlog hX h1 h2 h3
  have hXp : 0 < X := by linarith
  have hlogp : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogpow : (Real.log X)^3 ≤ c*X^(η/10) := by
    norm_num only [Real.rpow_ofNat] at hlog
    simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlogp.le 3),
      abs_of_nonneg (Real.rpow_nonneg hXp.le (η/10))] at hlog
    exact hlog
  have hmass : X^(1/2-η/10) ≤ c*Real.sqrt X/(Real.log X)^3 := by
    apply (le_div_iff₀ (pow_pos hlogp 3)).mpr
    calc
      _ ≤ X^(1/2-η/10)*(c*X^(η/10)) := mul_le_mul_of_nonneg_left hlogpow (by positivity)
      _ = c*Real.sqrt X := by
        rw [mul_left_comm _ c, ←Real.rpow_add hXp,
          show (1/2-η/10)+η/10 = (1/2 : ℝ) by ring, Real.sqrt_eq_rpow]
  refine ⟨by linarith,hlogp,le_trans ?_ hmass⟩
  rw [numericKernel_tail_powers hXp]
  have hp : X^(η/10)*X^(1/2-3*η) = X^(1/2-29*η/10) := by
    rw [←Real.rpow_add hXp]
    congr 1
    ring
  rw [hp]
  linarith

end Ostmann.QuadraticCenter

end

end OAI
