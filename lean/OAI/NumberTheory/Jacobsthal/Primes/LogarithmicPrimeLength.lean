import OAI.NumberTheory.Jacobsthal.Primes.HighPrimeRemoval

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.LogarithmicPrimeLength
open _root_.Filter
open ErdosPrimeInputs PrimeAbel PrimeEndpoints PrimeErrorDecay HarmonicPrimeMeasure PrimePrefixMass PrimePrefixTail

theorem fixed_log_length_tilt (C A L : ℝ) (hL : A+3 ≤ L*Real.log 2) :
    ∀ᶠ B : ℝ in atTop,∀ m : ℕ,L*Real.log B ≤ m →
      Real.exp (2*(Real.log B+C))/(2:ℝ)^m ≤ B^(-A) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (2*|C|))] with B hB hlog
  intro m hm
  have hBp : 0 < B := zero_lt_one.trans hB
  have hlog0 : 0 ≤ Real.log B := by linarith [le_max_left (1:ℝ) (2*|C|)]
  have hC : 2*C ≤ Real.log B := by linarith [le_max_right (1:ℝ) (2*|C|),le_abs_self C]
  have hm' := mul_le_mul_of_nonneg_right hm hlog2.le
  have hL' := mul_le_mul_of_nonneg_right hL hlog0
  have he : 2*(Real.log B+C)-(m:ℝ)*Real.log 2 ≤ Real.log B*(-A) := by nlinarith
  have hpow : (2:ℝ)^m=Real.exp ((m:ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [hpow,← Real.exp_sub,Real.rpow_def_of_pos hBp]
  exact Real.exp_le_exp.mpr he

theorem logarithmic_prime_length_tail : ∃ w₀ : ℝ,1 < w₀ ∧ ∀ A : ℝ,∃ L : ℝ,1 ≤ L ∧
    ∀ᶠ B : ℝ in atTop,∀ w : ℝ,w₀ ≤ w → ∀ m : ℕ,L*Real.log B ≤ m →
      longPrefixMass (primesBetween w (w^B)) m ≤ B^(-A) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hPrime⟩ := harmonic_prime_measure
  refine ⟨w₀,hw₀,?_⟩
  intro A
  let L := (|A|+4)/Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2up : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hL : 1 ≤ L := (le_div_iff₀ hlog2).mpr (by linarith [abs_nonneg A])
  have hcoef : A+3 ≤ L*Real.log 2 := by
    dsimp [L]
    rw [div_mul_cancel₀ _ hlog2.ne']
    linarith [le_abs_self A]
  refine ⟨L,hL,?_⟩
  filter_upwards [fixed_log_length_tilt C A L hcoef,eventually_ge_atTop (1:ℝ)] with B hTail hB
  intro w hw m hm
  have hw1 := hw₀.trans_le hw
  have hw0 : 0 < w := zero_lt_one.trans hw1
  have hab : w ≤ w^B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hw1.le hB
  have hh := hPrime w hw 1 B (by norm_num) hB false true
  rw [harmonicMass_eq_intervalSum hw1,Real.rpow_one,interval_open_closed hw0.le hab] at hh
  have hexp : Real.exp (-c*Real.sqrt (1*Real.log w)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (Real.sqrt_nonneg _))
  have hsum : (∑ p ∈ primesBetween w (w^B),(p:ℝ)⁻¹) ≤ Real.log B+C := by
    rw [sum_primesBetween hw0.le hab]
    have hu := (abs_le.mp hh).2
    simp only [Real.log_one,sub_zero] at hu
    linarith [mul_le_mul_of_nonneg_left hexp hC.le]
  calc
    _ ≤ Real.exp (2*∑ p ∈ primesBetween w (w^B),(p:ℝ)⁻¹)/(2:ℝ)^m := longPrefixMass_le _ _
    _ ≤ Real.exp (2*(Real.log B+C))/(2:ℝ)^m :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum (by norm_num))) (by positivity)
    _ ≤ _ := hTail m hm
end NumberTheoryLean.LogarithmicPrimeLength


end Erdos970

end OAI
