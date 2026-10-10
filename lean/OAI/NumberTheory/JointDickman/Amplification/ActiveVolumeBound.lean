import OAI.NumberTheory.JointDickman.Amplification.ActiveVolumeMajorant

namespace OAI

/-! # The active Cauchy volume is eventually at most 2 B / T -/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem activeVolumeMajorant_limit (B : ℕ) {T : ℕ} (hT : 0 < T) :
    Tendsto (activeVolumeMajorant B T) atTop (nhds
      (((∑ D ∈ (auxiliaryPrimes B).powerset,
        coefficientWeight B (∏ p ∈ D, p)/(∏ p ∈ D, (p : ℝ))) * baseArithmeticResidueMean B)/(T : ℝ))) := by
  have hlim : Tendsto (activeVolumeMajorant B T) atTop (nhds
      (∑ D ∈ (auxiliaryPrimes B).powerset, coefficientWeight B (∏ p ∈ D, p) *
        (baseArithmeticResidueMean B / ((T*(∏ p ∈ D, p) : ℕ) : ℝ)))) := by
    apply tendsto_finsetSum
    intro D hD
    have hd : 0 < ∏ p ∈ D, p := prod_pos (fun p hp =>
      (auxiliaryPrimes_prime B p (mem_powerset.mp hD hp)).pos)
    exact (mean_scaled_prefix (baseArithmeticResidueWeight_mean_tendsto B) (Nat.mul_pos hT hd)).const_mul _
  convert hlim using 1
  congr 1
  rw [sum_mul, sum_div]
  apply sum_congr rfl
  intro D hD
  have hd : (∏ p ∈ D, (p : ℝ)) ≠ 0 := prod_ne_zero_iff.mpr (fun p hp => by
    exact_mod_cast (auxiliaryPrimes_prime B p (mem_powerset.mp hD hp)).ne_zero)
  have ht : (T : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
  rw [Nat.cast_mul, Nat.cast_prod]
  field_simp

theorem activeFirstFormVolume_bound {B : ℕ} (hB : 1 < B) (L : ℕ) (τ C : ℝ)
    (u : ℕ → ℝ) {T : ℕ} (hT : 0 < T) (hu : ∀ c, u c ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᶠ N : ℕ in atTop, activeFirstFormVolume B L τ C u T N ≤ 2*(B : ℝ)/(T : ℝ) := by
  have hBp : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hTp : (0 : ℝ) < T := by exact_mod_cast hT
  have hb := div_le_div_of_nonneg_right (coefficient_harmonic_mul_residueMean_le hB) hTp.le
  have hstrict : ((∑ D ∈ (auxiliaryPrimes B).powerset,
      coefficientWeight B (∏ p ∈ D, p)/(∏ p ∈ D, (p : ℝ))) * baseArithmeticResidueMean B)/(T : ℝ) <
      2*(B : ℝ)/(T : ℝ) := by
    apply lt_of_le_of_lt hb
    rw [mul_div_assoc]
    have := div_pos hBp hTp
    linarith
  filter_upwards [(activeVolumeMajorant_limit B hT).eventually (eventually_le_nhds hstrict)] with N hN
  exact (activeFirstFormVolume_le_majorant B L τ C u hT N hu).trans hN

end JointDickman

end OAI
