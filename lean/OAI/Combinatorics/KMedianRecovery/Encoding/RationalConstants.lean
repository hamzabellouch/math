import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Cap

namespace OAI

namespace MetricKMedianRecovery.IntegralAssembly
noncomputable def countRat : ℚ := 10+(600/(1/100:ℚ))*2^(Anchoring.rounds (1/100)-1)
noncomputable def gapRat : ℚ := (1/(200*(200*countRat+2)))^2/100
noncomputable def gammaRat : ℚ := min (3/100) (gapRat/100)
lemma countRat_cast : (countRat:ℝ)=Anchoring.countConstant (1/100) := by
  simp only [countRat,Anchoring.countConstant,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one]
lemma gapRat_cast : (gapRat:ℝ)=strictnessGap (200*Anchoring.countConstant (1/100)) := by
  simp only [gapRat,strictnessGap,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one,countRat_cast]
lemma gammaRat_cast : (gammaRat:ℝ)=gamma := by
  simp only [gammaRat,gamma,Rat.cast_min,Rat.cast_div,Rat.cast_ofNat,gapRat_cast]
lemma gammaRat_pos : 0<gammaRat := by exact_mod_cast (show (0:ℝ)<(gammaRat:ℝ) by rw [gammaRat_cast]; exact gamma_pos)
lemma cap_rat (n : ℕ) : Rounding.cap n (gamma/16)=⌈20*(n:ℚ)^2/(gammaRat/16)⌉₊+1 := by
  unfold Rounding.cap
  congr 1
  rw [←gammaRat_cast]
  norm_cast
  rw [←Int.ceil_toNat,←Int.ceil_toNat,Rat.ceil_cast]
end MetricKMedianRecovery.IntegralAssembly

end OAI
