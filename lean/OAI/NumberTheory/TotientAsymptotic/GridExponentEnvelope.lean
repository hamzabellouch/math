import OAI.NumberTheory.TotientAsymptotic.CoordinateActivePrefix
import OAI.NumberTheory.TotientAsymptotic.PositiveGridCount

namespace OAI

/-! A common error envelope when the active coordinate prefix varies in length. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma countBandWeight_lower (r : ℕ) : 1-countBandWeight (r+1) ≤ ((r:ℝ)+2)^2 := by
  have hl : Real.log ((r:ℝ)+1) ≤ r := by
    simpa using Real.log_le_sub_one_of_pos (show 0 < (r:ℝ)+1 by positivity)
  have hr : 0 ≤ (r:ℝ) := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ (r:ℝ)+1 by positivity)
  simp only [countBandWeight,Nat.cast_add,Nat.cast_one]
  nlinarith

lemma grid_exponent_envelope {X r k K L : ℕ} {D T : ℝ}
    (hr : r ≤ k) (hD : 0 ≤ D) (hBS : 0 ≤ B (loglogCutoff L))
    (hK : (K:ℝ) ≤ B X+2) :
    -(T-((L:ℝ)+1)*(k:ℝ)^2)+(B X+5-K)*(∑ j : Fin r,a (j.val+1))+
      (1-countBandWeight (r+1))*B (loglogCutoff L)+D*(r:ℝ)*(r+2)+
        (r:ℝ)*(r+2)^2*Real.sqrt (B (loglogCutoff L)*K) ≤
    -T+(B X+L+6-K)*(k:ℝ)^2+((k:ℝ)+2)^2*B (loglogCutoff L)+
      D*((k:ℝ)+2)^2+((k:ℝ)+2)^3*Real.sqrt (B (loglogCutoff L)*K) := by
  have hr0 : 0 ≤ (r:ℝ) := Nat.cast_nonneg _
  have hk0 : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have hrk : (r:ℝ) ≤ k := Nat.cast_le.mpr hr
  have hcost : 0 ≤ B X+5-K := by linarith
  have hs : (∑ j : Fin r,a (j.val+1)) ≤ (k:ℝ)^2 :=
    (sum_a_fin_le_square r).trans (pow_le_pow_left₀ hr0 hrk 2)
  have hscore := mul_le_mul_of_nonneg_left hs hcost
  have hw : 1-countBandWeight (r+1) ≤ ((k:ℝ)+2)^2 :=
    (countBandWeight_lower r).trans (pow_le_pow_left₀ (by positivity) (by linarith) 2)
  have hweight := mul_le_mul_of_nonneg_right hw hBS
  have hdd : (r:ℝ)*(r+2) ≤ ((k:ℝ)+2)^2 := by nlinarith
  have hd := mul_le_mul_of_nonneg_left hdd hD
  have hrr : (r:ℝ)*(r+2)^2 ≤ ((k:ℝ)+2)^3 := by
    have hp := pow_le_pow_left₀ (show 0 ≤ (r:ℝ)+2 by positivity) (show (r:ℝ)+2 ≤ (k:ℝ)+2 by linarith) 2
    have hh := mul_le_mul hp (show (r:ℝ) ≤ (k:ℝ)+2 by linarith) hr0 (sq_nonneg _)
    nlinarith only [hh]
  have hroot := mul_le_mul_of_nonneg_right hrr (Real.sqrt_nonneg (B (loglogCutoff L)*K))
  nlinarith only [hscore,hweight,hd,hroot]

end TotientAsymptotic

end

end OAI
