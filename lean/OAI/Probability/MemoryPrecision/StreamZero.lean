import Mathlib
import OAI.Probability.GaussianRegression.Main

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision

lemma zero_cap_coefficient {d : ℕ} (hd : 32 ≤ d) :
    (3*4^d:ℝ) ≤ (20:ℝ)^(((d:ℝ)-1)/2) := by
  have hs : (9:ℝ)*16^d ≤ 20^(d-1) := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hd
    have he : 32+k-1 = 31+k := by omega
    rw [he, pow_add, pow_add]
    have hb : (9:ℝ)*16^32 ≤ 20^31 := by norm_num
    calc
      _ = ((9:ℝ)*16^32)*16^k := by ring
      _ ≤ 20^31*20^k := mul_le_mul hb (pow_le_pow_left₀ (by norm_num) (by norm_num : (16:ℝ) ≤ 20) k)
        (by positivity) (by positivity)
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  have hl : (3*4^d:ℝ)^2 = 9*16^d := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm d 2, pow_mul]
    norm_num
  have hr : ((20:ℝ)^(((d:ℝ)-1)/2))^2 = 20^(d-1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 20)]
    rw [← Real.rpow_natCast]
    congr 1
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    ring
  rwa [hl,hr]

lemma zero_cap_precise {d : ℕ} (hd : 32 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/10) :
    (3*4^d:ℝ)*ε^(d-1) ≤ (2*ε)^(((d:ℝ)-1)/2) := by
  let a := ((d:ℝ)-1)/2
  have ha : 0 ≤ a := by
    dsimp [a]
    have : (32:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have he : ε^(d-1) = ε^a*ε^a := by
    rw [← Real.rpow_add hε, ← Real.rpow_natCast]
    congr 1
    dsimp [a]
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    ring
  have hsmall : (10*ε)^a ≤ 1 := Real.rpow_le_one (by positivity) (by linarith) ha
  calc
    _ ≤ (20:ℝ)^a * ε^(d-1) := mul_le_mul_of_nonneg_right (zero_cap_coefficient hd) (by positivity)
    _ = (2*ε)^a*(10*ε)^a := by
      rw [he, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hε.le,
        Real.mul_rpow (by norm_num : (0:ℝ) ≤ 10) hε.le]
      have h20 := Real.mul_rpow (z := a) (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) ≤ 10)
      norm_num only [show (2:ℝ)*10=20 by norm_num] at h20
      rw [h20]
      ring
    _ ≤ (2*ε)^a * 1 := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = _ := mul_one _
end MemoryPrecision


end

end OAI
