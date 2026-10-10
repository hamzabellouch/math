import OAI.NumberTheory.JointDickman.Arithmetic.SubsquarePrimeSamples

namespace OAI

/-! # Elementary parameters for the growing prime moment -/
namespace JointDickman
open Finset TwoPointCorrelations
open scoped Classical

noncomputable def growingPrimeMoment (X M : ℝ) : ℕ := ⌊Real.log X/Real.log M⌋₊

lemma growingPrimeMoment_bounds {X M : ℝ} (hX : 1 ≤ X) (hM : 1 ≤ Real.log M)
    (hM0 : 0 < M) :
    M^(growingPrimeMoment X M) ≤ X ∧
      X ≤ M^(growingPrimeMoment X M+1) ∧
      (growingPrimeMoment X M:ℝ) ≤ Real.log X := by
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hlogM : 0 < Real.log M := by linarith
  have hX0 : 0 < X := by linarith
  have hfloor := Nat.floor_le (div_nonneg hlogX hlogM.le)
  have hceil := Nat.lt_floor_add_one (Real.log X/Real.log M)
  refine ⟨?_,?_,?_⟩
  · rw [← Real.rpow_natCast,Real.rpow_def_of_pos hM0]
    calc
      _ ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr (by
        have hh := (le_div_iff₀ hlogM).mp hfloor
        dsimp [growingPrimeMoment]
        nlinarith)
      _ = X := Real.exp_log hX0
  · rw [← Real.rpow_natCast,Real.rpow_def_of_pos hM0]
    calc
      X = Real.exp (Real.log X) := (Real.exp_log hX0).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hh := (div_lt_iff₀ hlogM).mp hceil
        dsimp [growingPrimeMoment]
        push_cast
        linarith)
  · exact hfloor.trans (div_le_self hlogX hM)

lemma growing_moment_mass {X M V : ℝ} {r : ℕ}
    (hlog : 3 ≤ Real.log X) (hM : 0 < M) (hlarge : (Real.log X)^100 ≤ M)
    (hr : (r:ℝ) ≤ Real.log X) (hV : M^(-1/6:ℝ) ≤ V)
    {A : ℝ} (hA : A ≤ 9/M) :
    (r:ℝ)*A ≤ M^(-5/8:ℝ)*V^2 := by
  have hl0 : 0 < Real.log X := by linarith
  have hroot : (Real.log X)^(25/6:ℝ) ≤ M^(1/24:ℝ) := by
    have hh := Real.rpow_le_rpow (pow_nonneg hl0.le 100) hlarge (by norm_num : (0:ℝ)≤1/24)
    rw [← Real.rpow_natCast,← Real.rpow_mul hl0.le] at hh
    norm_num at hh
    exact hh
  have hcube : (Real.log X)^3 ≤ (Real.log X)^(25/6:ℝ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hlow : 9*Real.log X ≤ M^(1/24:ℝ) := by
    have hp : 0 ≤ (Real.log X)*((Real.log X)-3)*((Real.log X)+3) := by positivity
    have hh : 9*Real.log X ≤ (Real.log X)^3 := by nlinarith
    exact hh.trans (hcube.trans hroot)
  have hnum : (r:ℝ)*9 ≤ M^(1/24:ℝ) := by linarith
  have hpow : M^(-1/3:ℝ) ≤ V^2 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hM.le (-1/6:ℝ)) hV 2
    rw [← Real.rpow_mul_natCast hM.le] at hh
    norm_num at hh
    simpa only [neg_div] using hh
  calc
    (r:ℝ)*A ≤ (r:ℝ)*(9/M) := mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg r)
    _ ≤ M^(1/24:ℝ)/M := by rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hnum hM.le
    _ = M^(-5/8:ℝ)*M^(-1/3:ℝ) := by
      rw [← Real.rpow_sub_one hM.ne',← Real.rpow_add hM]
      norm_num
    _ ≤ M^(-5/8:ℝ)*V^2 := mul_le_mul_of_nonneg_left hpow (by positivity)

end JointDickman

end OAI
