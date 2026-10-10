import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.RealContinuation

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision

def SuccessConstant : ℝ := 6*StepConstant
lemma successConstant_one : 1 ≤ SuccessConstant := by
  have h := stepConstant_one
  dsimp [SuccessConstant]
  linarith

lemma stopping_factor_bound {d : ℕ} (hd : 16 ≤ d) (T : ℕ) :
    (T+1:ℝ) ≤ ((2:ℝ)^d)^BlockCount T (d/8) := by
  have hT := blockCount_mul_ge T (by omega : 0 < d/8)
  have hp : d/8 ≤ d := Nat.div_le_self _ _
  have hTd : T ≤ d * BlockCount T (d/8) := by nlinarith
  have htwo : (T+1:ℕ) ≤ 2^T := Nat.lt_two_pow_self
  have hpow : (2:ℝ)^T ≤ 2^(d * BlockCount T (d/8)) :=
    pow_le_pow_right₀ (by norm_num) hTd
  rw [pow_mul] at hpow
  exact (by exact_mod_cast htwo : (T+1:ℝ) ≤ (2:ℝ)^T).trans hpow

lemma stopping_step_bound {d N K : ℕ} (hd : 16 ≤ d) (hN : 1 ≤ N) (hNK : N ≤ K)
    (T : ℕ) :
    (T+1:ℝ) * RealStep d N ^ BlockCount T (d/8) ≤
      ((2*StepConstant)^d * (K:ℝ)^(1/((d/8:ℕ):ℝ))) ^ BlockCount T (d/8) := by
  have hSp := stepConstant_pos
  have hR := realStep_pos d hN
  have hn0 : (0:ℝ) ≤ N := by positivity
  have hroot : (N:ℝ)^(1/((d/8:ℕ):ℝ)) ≤ (K:ℝ)^(1/((d/8:ℕ):ℝ)) :=
    Real.rpow_le_rpow hn0 (by exact_mod_cast hNK) (by positivity)
  calc
    _ ≤ ((2:ℝ)^d)^BlockCount T (d/8) * RealStep d N ^ BlockCount T (d/8) :=
      mul_le_mul_of_nonneg_right (stopping_factor_bound hd T) (by positivity)
    _ = ((2*StepConstant)^d * (N:ℝ)^(1/((d/8:ℕ):ℝ))) ^ BlockCount T (d/8) := by
      rw [← mul_pow]
      congr 1
      simp only [RealStep, mul_pow]
      ring
    _ ≤ _ := pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_left hroot (by positivity)) _

lemma stopping_step_bound_three {d N K T : ℕ} (hd : 16 ≤ d) (hN : 1 ≤ N)
    (hNK : N ≤ K) (hT : 0 < T) :
    3 * ((T+1:ℝ) * RealStep d N ^ BlockCount T (d/8)) ≤
      (SuccessConstant^d * (K:ℝ)^(1/((d/8:ℕ):ℝ))) ^ BlockCount T (d/8) := by
  have hSp := stepConstant_pos
  have hR := realStep_pos d hN
  have hb := blockCount_pos hT (by omega : 0 < d/8)
  have h3 : (3:ℝ) ≤ ((3:ℝ)^d)^BlockCount T (d/8) := by
    rw [← pow_mul]
    have hdb : 1 ≤ d * BlockCount T (d/8) := Nat.mul_pos (by omega) hb
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) hdb
  have hroot0 : 0 ≤ (K:ℝ)^(1/((d/8:ℕ):ℝ)) := by positivity
  calc
    _ ≤ ((3:ℝ)^d)^BlockCount T (d/8) *
        ((2*StepConstant)^d * (K:ℝ)^(1/((d/8:ℕ):ℝ))) ^ BlockCount T (d/8) :=
      mul_le_mul h3 (stopping_step_bound hd hN hNK T)
        (by positivity) (by positivity)
    _ = _ := by
      rw [← mul_pow]
      congr 1
      rw [← mul_assoc, ← mul_pow]
      congr 2
      dsimp [SuccessConstant]
      ring

lemma cap_constant_le {d : ℕ} (hd : 1 ≤ d) : (3*4^d:ℝ) ≤ 12^d := by
  have h3 : (3:ℝ) ≤ 3^d := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) hd
  calc
    _ ≤ 3^d*4^d := mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = _ := by rw [← mul_pow]; norm_num

lemma terminal_angular_zero_bound {d : ℕ} (hd : 16 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1/10) :
    (3*4^d:ℝ)*ε^(d-1) ≤ 4^d*ε^(((d:ℝ)-1)/2) := by
  have hd' : (16:ℝ) ≤ d := by exact_mod_cast hd
  have hα : (1:ℝ) ≤ ((d:ℝ)-1)/2 := by linarith
  have hεa : ε^(((d:ℝ)-1)/2) ≤ ε := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hε (by linarith : ε ≤ 1) hα
  have hn : ((d-1:ℕ):ℝ) = (d:ℝ)-1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have he : ε^(d-1) = ε^(((d:ℝ)-1)/2) * ε^(((d:ℝ)-1)/2) := by
    rw [← Real.rpow_add hε, ← Real.rpow_natCast, hn]
    congr 1
    ring
  rw [he]
  have haux : 3*ε^(((d:ℝ)-1)/2) ≤ 1 := by linarith
  calc
    _ = (4^d*ε^(((d:ℝ)-1)/2)) * (3*ε^(((d:ℝ)-1)/2)) := by ring
    _ ≤ (4^d*ε^(((d:ℝ)-1)/2)) * 1 := mul_le_mul_of_nonneg_left haux (by positivity)
    _ = _ := mul_one _

end MemoryPrecision


end

end OAI
