import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.CubeContinuation

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision

lemma cube_memory_ratio {d M : ℕ} (hd : 16 ≤ d) (hM : M ≤ d^2) :
    (M:ℝ) / (((d/2)/4:ℕ):ℝ) ≤ 72 * (d/2:ℕ) := by
  have hd3 : d ≤ 3*(d/2) := by omega
  have hn8 : d/2 ≤ 8*((d/2)/4) := by omega
  have hm : M ≤ (72*(d/2))*((d/2)/4) := by
    calc
      M ≤ d^2 := hM
      _ ≤ (3*(d/2))^2 := Nat.pow_le_pow_left hd3 2
      _ = 9*(d/2)*(d/2) := by ring
      _ ≤ 9*(d/2)*(8*((d/2)/4)) := Nat.mul_le_mul_left _ hn8
      _ = _ := by ring
  apply (div_le_iff₀ (by exact_mod_cast (show 0 < (d/2)/4 by omega))).2
  exact_mod_cast hm

lemma cube_memory_factor {d M : ℕ} (hd : 16 ≤ d) (hM : M ≤ d^2) :
    ((2^M:ℕ):ℝ)^(1/(((d/2)/4:ℕ):ℝ)) ≤ ((2:ℝ)^72)^(d/2) := by
  have he : ((2^M:ℕ):ℝ)^(1/(((d/2)/4:ℕ):ℝ)) =
      (2:ℝ)^((M:ℝ)/(((d/2)/4:ℕ):ℝ)) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  rw [he, ← pow_mul, ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
  simpa using cube_memory_ratio hd hM

lemma cube_stopping_factor {d : ℕ} (hd : 16 ≤ d) (T : ℕ) :
    (T+1:ℝ) ≤ ((2:ℝ)^(d/2))^BlockCount T ((d/2)/4) := by
  have hT := blockCount_mul_ge T (by omega : 0 < (d/2)/4)
  have hp : (d/2)/4 ≤ d/2 := Nat.div_le_self _ _
  have hTn : T ≤ (d/2) * BlockCount T ((d/2)/4) := by nlinarith
  have htwo : (T+1:ℕ) ≤ 2^T := Nat.lt_two_pow_self
  have hpow : (2:ℝ)^T ≤ 2^((d/2) * BlockCount T ((d/2)/4)) :=
    pow_le_pow_right₀ (by norm_num) hTn
  rw [pow_mul] at hpow
  exact (by exact_mod_cast htwo : (T+1:ℝ) ≤ (2:ℝ)^T).trans hpow

def CubeSuccessConstant : ℝ := max 12 (2*CubeStepConstant*2^72)
lemma cubeSuccessConstant_twelve : 12 ≤ CubeSuccessConstant := le_max_left _ _
lemma cubeSuccessConstant_one : 1 ≤ CubeSuccessConstant :=
  (by norm_num : (1:ℝ) ≤ 12).trans cubeSuccessConstant_twelve
lemma cubeSuccessConstant_exp : Real.exp 1 ≤ CubeSuccessConstant :=
  Real.exp_one_lt_three.le.trans ((by norm_num : (3:ℝ) ≤ 12).trans cubeSuccessConstant_twelve)
lemma cubeSuccessConstant_pos : 0 < CubeSuccessConstant :=
  lt_of_lt_of_le zero_lt_one cubeSuccessConstant_one

lemma cube_whole_factor {d M : ℕ} (hd : 16 ≤ d) (hM : M ≤ d^2) (T : ℕ) :
    (T+1:ℝ) * ((12:ℝ)^(d/2) * CubeStep d (2^M) ^ BlockCount T ((d/2)/4)) ≤
      CubeSuccessConstant^((d/2)*(BlockCount T ((d/2)/4)+1)) := by
  have hC := cubeStepConstant_pos
  have hD := cubeSuccessConstant_pos
  have hS := cubeStep_pos d (show 1 ≤ 2^M by exact one_le_pow₀ (by norm_num))
  have hmem := cube_memory_factor hd hM
  have hstep : (2:ℝ)^(d/2) * CubeStep d (2^M) ≤ CubeSuccessConstant^(d/2) := by
    calc
      _ ≤ 2^(d/2) * (CubeStepConstant^(d/2) * ((2:ℝ)^72)^(d/2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmem (by positivity)) (by positivity)
      _ = (2*CubeStepConstant*2^72)^(d/2) := by simp only [mul_pow]; ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
  calc
    _ = 12^(d/2) * ((T+1:ℝ) * CubeStep d (2^M) ^ BlockCount T ((d/2)/4)) := by ring
    _ ≤ 12^(d/2) * (((2:ℝ)^(d/2))^BlockCount T ((d/2)/4) *
        CubeStep d (2^M) ^ BlockCount T ((d/2)/4)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (cube_stopping_factor hd T) (by positivity))
        (by positivity)
    _ = 12^(d/2) * ((2:ℝ)^(d/2) * CubeStep d (2^M))^BlockCount T ((d/2)/4) := by rw [mul_pow]
    _ ≤ CubeSuccessConstant^(d/2) * (CubeSuccessConstant^(d/2))^BlockCount T ((d/2)/4) :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num) cubeSuccessConstant_twelve _)
        (pow_le_pow_left₀ (by positivity) hstep _) (by positivity) (by positivity)
    _ = _ := by rw [pow_mul, pow_succ]; ring
end MemoryPrecision


end

end OAI
