import OAI.NumberTheory.TotientAsymptotic.GridApproximation
import OAI.NumberTheory.TotientAsymptotic.ConcentrationTail

namespace OAI

/-! The reciprocal-prime box error absorbs the complete cofactor envelope. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma cofactor_bandPrimeError_tendsto (K : ℝ) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    Tendsto (fun H => Real.exp (K*cofactorScale H)*bandPrimeError C c H) atTop (nhds 0) := by
  have hq : Real.exp (-c*lam) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [lam_pos]
  have ht : Tendsto (fun H : ℕ => C*(Real.exp (-c*lam)^H/(1-Real.exp (-c*lam))))
      atTop (nhds 0) := by
    simpa only [zero_div, mul_zero] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le hq).div_const
        (1-Real.exp (-c*lam))).const_mul C
  have hg := cofactor_concentration_tail_tendsto K
    (c := 2*c*lam) (mul_pos (mul_pos (by norm_num) hc) lam_pos)
  have he : -(2*c*lam)/2 = -c*lam := by ring
  rw [he] at hg
  apply squeeze_zero' (g := fun H => (2*C)*(Real.exp (K*cofactorScale H)*
    Real.exp (-c*lam)^H/(1-Real.exp (-c*lam))))
  · exact Eventually.of_forall (fun H => mul_nonneg (Real.exp_pos _).le (bandPrimeError_nonneg hC hc H))
  · filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1))] with H hH
    have hnon : 0 ≤ C*(Real.exp (-c*lam)^H/(1-Real.exp (-c*lam))) := by positivity
    have hb := Real.abs_exp_sub_one_le (by rw [abs_of_nonneg hnon]; exact hH.le)
    have hb' := (le_abs_self _).trans hb
    rw [abs_of_nonneg hnon] at hb'
    have hm := mul_le_mul_of_nonneg_left hb' (Real.exp_pos (K*cofactorScale H)).le
    change Real.exp (K*cofactorScale H)*(Real.exp _-1) ≤ _
    exact hm.trans_eq (by ring)
  · simpa only [mul_zero] using hg.const_mul (2*C)

end TotientAsymptotic

end

end OAI
