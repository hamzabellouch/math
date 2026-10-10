import OAI.NumberTheory.JointDickman.Arithmetic.HighBinPrimeWeight
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeAvoidanceDegreeLimit

namespace OAI

/-! # Identification of the high-bin generating value -/
namespace JointDickman
open Finset Filter Erdos970.NumberTheoryLean
open scoped Topology

 theorem highBinGenerating_eq_dickman {J k : ℕ} (hJ : 2 ≤ J) (hk : 0 < k) (hkJ : k < J) :
    binGeneratingLimit J (highBinZeroWeight J k) = Dickman.rho (1/((k : ℝ)/J)) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hc : 0 < (k : ℝ)/J := div_pos hkr hJr
  have hc1 : (k : ℝ)/J < 1 := (div_lt_one hJr).mpr (by exact_mod_cast hkJ)
  have hd (h : ℕ) : Tendsto (fun x =>
      primeGeneratingDegree (largePrimeSet x (x^((1 : ℝ)/J)))
        (primeBinWeight J (highBinZeroWeight J k) x) ⌊x⌋₊ h)
      atTop (𝓝 ((-1 : ℝ)^h*logarithmicSimplex h ((k : ℝ)/J))) := by
    cases h with
    | zero =>
      simp only [pow_zero, logarithmicSimplex_zero, mul_one]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      exact (primeGeneratingDegree_zero _ _ (Nat.floor_pos.mpr hx)).symm
    | succ n =>
      apply (primeAvoidanceDegree_tendsto hc hc1 n).congr'
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      exact (highBinPrimeDegree hJ hk hx ⌊x⌋₊ (n+1)).symm
  have ht := tendsto_finsetSum (range (J+1)) (fun h _ => hd h)
  have hm : Tendsto (fun x => primeGeneratingModel (largePrimeSet x (x^((1 : ℝ)/J)))
      (primeBinWeight J (highBinZeroWeight J k) x) ⌊x⌋₊)
      atTop (𝓝 (logarithmicAvoidance J ((k : ℝ)/J))) := by
    apply ht.congr'
    filter_upwards [bounded_largePrimeSubsets_eventually J (by omega : 0 < J) 1,
      eventually_ge_atTop (1 : ℝ)] with x hcard hx
    rw [one_mul, allLargeBinPrimes_eq_largePrimeSet J (zero_le_one.trans hx)] at hcard
    exact (primeGeneratingModel_sum_degree _ _ _ J hcard).symm
  have hp := primeGeneratingModel_bin_tendsto hJ (highBinZeroWeight J k) zero_lt_one
  simp only [one_mul] at hp
  rw [tendsto_nhds_unique hp hm]
  apply logarithmicAvoidance_eq_dickman J hc
  rw [one_div_div]
  apply (div_le_iff₀ hkr).mpr
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith [hJr.le]

end JointDickman

end OAI
