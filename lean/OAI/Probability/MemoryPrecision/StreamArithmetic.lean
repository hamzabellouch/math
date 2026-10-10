import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.SuccessArithmetic

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision

def StreamConstant : ℝ := 3*(SuccessConstant+21)
lemma streamConstant_pos : 0 < StreamConstant := by
  have h := successConstant_one
  dsimp [StreamConstant]
  linarith

lemma blockCount_antitone {p q : ℕ} (hq : 0 < q) (hqp : q ≤ p) (T : ℕ) :
    BlockCount T p ≤ BlockCount T q := by
  apply Nat.ceil_mono
  exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hq) (by exact_mod_cast hqp)

lemma power_le_exp {x : ℝ} (hx : 0 ≤ x) (d : ℕ) : x^d ≤ Real.exp (x*d) := by
  have hl : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have h := pow_le_pow_left₀ hx hl d
  simpa only [← Real.rpow_natCast, ← Real.exp_mul] using h

lemma stream_root_exp {d M : ℕ} (hd : 32 ≤ d) :
    (((d/8+2)*2^M:ℕ):ℝ)^(1/((d/8:ℕ):ℝ)) ≤ Real.exp ((d:ℝ)+16*M/d) := by
  have hn : (d/8+2)*2^M ≤ 2^(d+M) := by
    have h : d/8+2 ≤ 2^d := (show d/8+2 ≤ d+1 by omega).trans Nat.lt_two_pow_self
    simpa [pow_add] using Nat.mul_le_mul_right (2^M) h
  have ht : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hnum : (((d/8+2)*2^M:ℕ):ℝ) ≤ Real.exp ((d:ℝ)+M) := by
    calc
      _ ≤ (2:ℝ)^(d+M) := by exact_mod_cast hn
      _ ≤ (Real.exp 1)^(d+M) := pow_le_pow_left₀ (by norm_num) ht _
      _ = _ := by rw [← Real.rpow_natCast, ← Real.exp_mul]; simp
  have hdp : (d:ℝ)/16 ≤ (d/8:ℕ) := by
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 16)).2
    exact_mod_cast (show d ≤ (d/8)*16 by omega)
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hr : ((d:ℝ)+M)/((d/8:ℕ):ℝ) ≤ (d:ℝ)+16*M/d := by
    calc
      _ ≤ ((d:ℝ)+M)/((d:ℝ)/16) := div_le_div_of_nonneg_left (by positivity) (by positivity) hdp
      _ = 16+16*M/d := by field_simp
      _ ≤ _ := by
        have : (16:ℝ) ≤ d := by exact_mod_cast (show 16 ≤ d by omega)
        linarith
  calc
    _ ≤ (Real.exp ((d:ℝ)+M))^(1/((d/8:ℕ):ℝ)) :=
      Real.rpow_le_rpow (by positivity) hnum (by positivity)
    _ = Real.exp (((d:ℝ)+M)/((d/8:ℕ):ℝ)) := by rw [← Real.exp_mul]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr hr

lemma stream_step_exp {d M : ℕ} (hd : 32 ≤ d) :
    SuccessConstant^d * (((d/8+2)*2^M:ℕ):ℝ)^(1/((d/8:ℕ):ℝ)) ≤
      Real.exp ((d:ℝ)*(SuccessConstant+1)+16*M/d) := by
  have hS := successConstant_one
  calc
    _ ≤ Real.exp (SuccessConstant*d) * Real.exp ((d:ℝ)+16*M/d) :=
      mul_le_mul (power_le_exp (by linarith) d) (stream_root_exp hd) (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma stream_step_one (d M : ℕ) :
    1 ≤ SuccessConstant^d * (((d/8+2)*2^M:ℕ):ℝ)^(1/((d/8:ℕ):ℝ)) := by
  apply one_le_mul_of_one_le_of_one_le (one_le_pow₀ successConstant_one)
  apply Real.one_le_rpow _ (by positivity)
  exact_mod_cast (show 1 ≤ (d/8+2)*2^M by
    exact Nat.succ_le_iff.mpr (Nat.mul_pos (by omega) (by positivity)))

lemma stream_exponent_bound {d M : ℕ} (hd : 32 ≤ d) :
    (d:ℝ)*(SuccessConstant+5)+16*M/d ≤
      (((d:ℝ)-1)/2)*StreamConstant*(1+(M:ℝ)/(d:ℝ)^2) := by
  have hS := successConstant_one
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd3 : (d:ℝ)/3 ≤ ((d:ℝ)-1)/2 := by
    have : (32:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hc : 0 ≤ StreamConstant := streamConstant_pos.le
  calc
    _ ≤ (SuccessConstant+21)*(d:ℝ)+(SuccessConstant+21)*(M/d) := by
      have hM : 0 ≤ (M:ℝ)/d := by positivity
      have hm := mul_le_mul_of_nonneg_right (show (16:ℝ) ≤ SuccessConstant+21 by linarith) hM
      have hn : (d:ℝ)*(SuccessConstant+5) ≤ (SuccessConstant+21)*(d:ℝ) := by nlinarith
      simpa only [mul_div_assoc] using add_le_add hn hm
    _ = (d:ℝ)/3*StreamConstant*(1+(M:ℝ)/(d:ℝ)^2) := by
      dsimp [StreamConstant]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd3 hc) (by positivity)

lemma stream_full_factor {d M T : ℕ} (hd : 32 ≤ d) (hT : 0 < T) :
    (4:ℝ)^d * (SuccessConstant^d * (((d/8+2)*2^M:ℕ):ℝ)^(1/((d/8:ℕ):ℝ)))^BlockCount T (d/8) ≤
      Real.exp ((((d:ℝ)-1)/2)*StreamConstant*(1+(M:ℝ)/(d:ℝ)^2)*(BlockCount T ((d-1)/8):ℝ)) := by
  let b := BlockCount T ((d-1)/8)
  let K := SuccessConstant^d * (((d/8+2)*2^M:ℕ):ℝ)^(1/((d/8:ℕ):ℝ))
  have hK : 1 ≤ K := stream_step_one d M
  have hb : 1 ≤ b := blockCount_pos hT (by omega)
  have hbp : BlockCount T (d/8) ≤ b := blockCount_antitone (by omega) (by omega) T
  have h4 : (4:ℝ)^d ≤ Real.exp (4*d*(b:ℝ)) := by
    apply (power_le_exp (by norm_num : (0:ℝ) ≤ 4) d).trans
    apply Real.exp_le_exp.mpr
    exact le_mul_of_one_le_right (by positivity) (by exact_mod_cast hb)
  have hpow : K^b ≤ Real.exp (((d:ℝ)*(SuccessConstant+1)+16*M/d)*(b:ℝ)) := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ K) (stream_step_exp hd) b
    simpa only [← Real.rpow_natCast, ← Real.exp_mul, K] using h
  calc
    _ ≤ (4:ℝ)^d * K^b := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK hbp) (by positivity)
    _ ≤ Real.exp (4*d*(b:ℝ)) * Real.exp (((d:ℝ)*(SuccessConstant+1)+16*M/d)*(b:ℝ)) :=
      mul_le_mul h4 hpow (by positivity) (by positivity)
    _ = Real.exp (((d:ℝ)*(SuccessConstant+5)+16*M/d)*(b:ℝ)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (stream_exponent_bound hd) (by positivity))

end MemoryPrecision


end

end OAI
