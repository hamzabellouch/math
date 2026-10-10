import OAI.NumberTheory.Ostmann.Conclusion.FinalRateAbsorptionBasic

namespace OAI

noncomputable section
namespace Ostmann.Conclusion
open Filter
open scoped Topology

theorem eventually_final_sqrt_reserve {k : ℕ} (hk : 1 ≤ k) :
    ∀ᶠ L : ℝ in atTop,
      (2 : ℝ)^k * Real.sqrt (bulkSize k L) + (bulkSize k L : ℝ) ≤
        (2 : ℝ)^k * (bulkSize k L : ℝ) := by
  filter_upwards [(bulkSize_tendsto_atTop (by omega : 0 < k)).eventually_ge_atTop 4]
    with L hm
  have hr : (2 : ℝ) ≤ (2 : ℝ)^k := le_self_pow₀ (by norm_num) (by omega)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (bulkSize k L))
  have hs : Real.sqrt (bulkSize k L) ≤ (bulkSize k L : ℝ)/2 := by
    nlinarith [sq_nonneg (Real.sqrt (bulkSize k L)-2)]
  have hmul := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ (2 : ℝ)^k)
  have hmul' := mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg (bulkSize k L))
  nlinarith

theorem eventually_final_prefactor (R0 : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ∀ᶠ L : ℝ in atTop,
      3*R0*(((2 : ℝ)^k)^(2*(2^k))+1) ≤
        Real.exp ((2 : ℝ)^k*(bulkSize k L : ℝ)) := by
  have hbulk := bulkSize_tendsto_atTop (by omega : 0 < k)
  have hmul := hbulk.const_mul_atTop (by positivity : (0 : ℝ) < (2 : ℝ)^k)
  exact (Real.tendsto_exp_atTop.comp hmul).eventually_ge_atTop _

theorem eventually_final_bad_exponent {Bs BD Bz : ℝ}
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz)
    (B C : ℝ) {k : ℕ} (hk : 1 ≤ k)
    (hrate : finalRate BD Bs Bz (C+2) k < -2*B-4) :
    ∀ᶠ L : ℝ in atTop,
      frequencyBudget Bs BD Bz k L k +
        (2-(3/4 : ℝ)*Real.log ((2 : ℝ)^k))*(2 : ℝ)^k*(bulkSize k L : ℝ) +
        ((2 : ℝ)^k*(initialGap Bs k L+C*(bulkSize k L : ℝ))+(bulkSize k L : ℝ)) ≤
      -(2*B+3)*(2 : ℝ)^k*(bulkSize k L : ℝ) := by
  filter_upwards [eventually_final_sqrt_reserve hk] with L hs
  have hmain := final_bad_exponent_le hBs hBD hBz C hk L
  have hm := mul_le_mul_of_nonneg_right hrate.le
    (by positivity : (0 : ℝ) ≤ (2 : ℝ)^k*(bulkSize k L : ℝ))
  nlinarith

end Ostmann.Conclusion

end

end OAI
