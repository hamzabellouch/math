import Mathlib
import OAI.Computability.MinUncut.Model

namespace OAI

section
namespace MinUncut.FiniteGaussian

def algebraicNonneg (a b : ℚ) (N : ℕ) : Bool :=
  if 0 ≤ b then
    if 0 ≤ a then true else decide (a^2 ≤ (N:ℚ)*b^2)
  else
    if a < 0 then false else decide ((N:ℚ)*b^2 ≤ a^2)

lemma algebraicNonneg_eq (a b : ℚ) (N : ℕ) :
    algebraicNonneg a b N = true ↔ 0 ≤ (a:ℝ)+(b:ℝ)*Real.sqrt (N:ℝ) := by
  have hs := Real.sqrt_nonneg (N:ℝ)
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
  have hb2 : ((b:ℝ)*Real.sqrt (N:ℝ))^2=(N:ℝ)*(b:ℝ)^2 := by rw [mul_pow,hs2]; ring
  unfold algebraicNonneg
  split_ifs with hb ha ha
  · have hbr : (0:ℝ) ≤ b := by exact_mod_cast hb
    have har : (0:ℝ) ≤ a := by exact_mod_cast ha
    simp only [true_iff]
    positivity
  · have hbr : (0:ℝ) ≤ b := by exact_mod_cast hb
    have har : (a:ℝ) < 0 := by exact_mod_cast (lt_of_not_ge ha)
    have hprod : 0 ≤ (b:ℝ)*Real.sqrt (N:ℝ) := mul_nonneg hbr hs
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      have h' : (a:ℝ)^2 ≤ (N:ℝ)*(b:ℝ)^2 := by exact_mod_cast h
      nlinarith
    · intro h
      have h' : (a:ℝ)^2 ≤ (N:ℝ)*(b:ℝ)^2 := by nlinarith
      exact_mod_cast h'
  · have hbr : (b:ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hb)
    have har : (a:ℝ) < 0 := by exact_mod_cast ha
    have hprod : (b:ℝ)*Real.sqrt (N:ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hbr.le hs
    simp only [false_iff,not_le]
    linarith
  · have hbr : (b:ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hb)
    have har : (0:ℝ) ≤ a := by exact_mod_cast (le_of_not_gt ha)
    have hprod : (b:ℝ)*Real.sqrt (N:ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hbr.le hs
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      have h' : (N:ℝ)*(b:ℝ)^2 ≤ (a:ℝ)^2 := by exact_mod_cast h
      nlinarith
    · intro h
      have h' : (N:ℝ)*(b:ℝ)^2 ≤ (a:ℝ)^2 := by nlinarith
      exact_mod_cast h'

end MinUncut.FiniteGaussian

end

end OAI
