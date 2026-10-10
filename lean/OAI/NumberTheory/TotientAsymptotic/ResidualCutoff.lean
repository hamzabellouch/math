import OAI.NumberTheory.TotientAsymptotic.SmoothSuffix

namespace OAI

/-! The residual smoothness cutoff follows from the actual coarse prime bands. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- The lower edge used for the residual integer in the comparison lemma. -/
def residualCutoff (x : ℝ) (j : ℕ) : ℝ :=
  Real.exp (Real.exp ((7/10 : ℝ)*bandScale x j))

lemma next_band_below_residual_cutoff {x : ℝ} {j : ℕ} (hj : j < m x) :
    (11/10 : ℝ)*bandScale x (j+1) < (7/10 : ℝ)*bandScale x j := by
  have hs := bandScale_succ_le x j
  have hp := bandScale_pos hj
  have hr := collision_rho_bounds.2
  nlinarith

/-- No normality or squarefreeness is needed for residual smoothness. -/
theorem basic_residual_smooth {x : ℝ} {H j : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hL : L x H < m x) (hj : j < L x H) :
    (largestPrimeFactor (suffixPreimage η j).totient : ℝ) < residualCutoff x j := by
  have hj' : j+1 ∈ Finset.Icc 1 (L x H) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hp := hη.2.1 (j+1) hj'
  have hpos : (1 : ℝ) < remainderPrime η (j+1) := by exact_mod_cast hp.1.one_lt
  have hcoord : B (remainderPrime η (j+1)) < (7/10 : ℝ)*bandScale x j := by
    have hu := hp.2.2
    simp only [remainderCoord, Nat.add_one_ne_zero, ↓reduceIte] at hu
    exact hu.trans_lt (next_band_below_residual_cutoff (hj.trans hL))
  have hprime : (remainderPrime η (j+1) : ℝ) < residualCutoff x j := by
    apply (Real.log_lt_iff_lt_exp (zero_lt_one.trans hpos)).mp
    exact (Real.log_lt_iff_lt_exp (Real.log_pos hpos)).mp hcoord
  exact lt_of_le_of_lt (by exact_mod_cast basic_suffix_totient_smooth hη hL hj) hprime

end TotientAsymptotic

end

end OAI
