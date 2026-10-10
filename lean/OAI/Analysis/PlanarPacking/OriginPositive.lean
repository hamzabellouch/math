import OAI.Analysis.PlanarPacking.OriginIdentity
import OAI.Analysis.PlanarPacking.SignCaps
import OAI.Analysis.PlanarPacking.Certificate.HighMoments0_0
import OAI.Analysis.PlanarPacking.Certificate.HighMoments0_4
import OAI.Analysis.PlanarPacking.BernsteinBoxes

namespace OAI

/-! # Positivity at the origin of the exact Fourier pair -/

namespace SharpPlanar
open IntegerIntervals CachedData
lemma exactJet_zero_H₁ (s : ℝ) : exactJet false 0 s=H₁ s := by
  simp only [exactJet,exactData,Bool.false_eq_true,ite_false,Bool.not_false,ite_true,← cardinal_eq_cardinalSeries,H₁]
lemma exactJet_zero_H₂ (s : ℝ) : exactJet true 0 s=H₂ s := by
  simp only [exactJet,exactData,ite_true,Bool.not_true,Bool.false_eq_true,ite_false,← cardinal_eq_cardinalSeries,H₂]
lemma tableOrigin_lower : (3:ℝ)<tableHJet true 0 0 := by
  have hh := RBox.contains_add hm0_1_0_0.realContains hm0_0_1_0.realContains
  have hl := @RBox.lower_lt _ _ 3 1 hh (by norm_num) (by decide +kernel)
  simpa only [fullMoment_direct,fullMoment_transformed,Nat.factorial_zero,Nat.cast_one,div_one,one_div,tableHJet,Bool.not_true,Int.cast_ofNat,Int.cast_one,div_one] using hl
lemma exactRight_origin_positive : 0<exactRight 0 := by
  have he:=error_zero_cap true (show (0:ℝ)≤0 by norm_num)
  have hl:=tableOrigin_lower
  have hh:= (abs_lt.mp he).1
  rw [exactJet_zero_H₂] at hh
  rw [exactRight_apply]
  norm_num only [norm_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero,Real.exp_zero,one_mul]
  linarith
lemma exactLeft_origin_positive : 0<exactLeft 0 := by rw [exact_origin_identity]; exact exactRight_origin_positive
end SharpPlanar

end OAI
