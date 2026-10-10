import OAI.Combinatorics.ParityLifts.UniformRates

namespace OAI

namespace ParityWL.Complexity

lemma trial_race_numeric (A C r : ℝ) (d e j k L N s t : ℕ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hs : (s : ℝ) ≤ C*(L+1 : ℝ)^e*2^(r*N))
    (ht : (t : ℝ) ≤ A*(s+j+k+L+2 : ℝ)^d) :
    (t : ℝ) ≤ A*(C+j+k+3 : ℝ)^d*(L+1 : ℝ)^((e+1)*d)*2^((r*d)*N) := by
  let X : ℝ := (L+1 : ℝ)^(e+1)*2^(r*N)
  have hL : (1 : ℝ) ≤ L+1 := by have := Nat.cast_nonneg (α:=ℝ) L; linarith
  have hExp : (1 : ℝ) ≤ 2^(r*N) := Real.one_le_rpow (by norm_num) (by positivity)
  have hXp : (1 : ℝ) ≤ (L+1 : ℝ)^(e+1) := one_le_pow₀ hL
  have hX : 1 ≤ X := by dsimp only [X]; nlinarith
  have hLs : (L : ℝ) ≤ X := by
    calc
      _ ≤ (L+1 : ℝ)^1 := by simp
      _ ≤ (L+1 : ℝ)^(e+1) := pow_le_pow_right₀ hL (by omega)
      _ ≤ X := le_mul_of_one_le_right (by positivity) hExp
  have hCT : C*(L+1 : ℝ)^e*2^(r*N) ≤ C*X := by
    dsimp only [X]
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (show e ≤ e+1 by omega)) hC) (Real.rpow_nonneg (by norm_num) _)
  have hsum : (s+j+k+L+2 : ℝ) ≤ (C+j+k+3)*X := by
    have hn : (0 : ℝ) ≤ j+k+2 := by positivity
    have hconst := mul_le_mul_of_nonneg_left hX hn
    nlinarith
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ s+j+k+L+2) hsum d
  have he : ((2 : ℝ)^(r*N))^d=2^((r*d)*N) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num)]
    congr 1
    ring
  calc
    _ ≤ A*((C+j+k+3)*X)^d := ht.trans (mul_le_mul_of_nonneg_left hpow hA)
    _ = _ := by dsimp only [X]; rw [mul_pow,mul_pow,←pow_mul,he]; ring

end ParityWL.Complexity

end OAI
