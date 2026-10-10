import OAI.NumberTheory.JointDickman.Amplification.GeneratingBinExpansion
import OAI.NumberTheory.JointDickman.Amplification.GeneratingFloorLimit

namespace OAI

/-! # Unconditional limits of the finite-bin generating polynomials -/
namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def binDegreeLimit (J : ℕ) (z : Fin (J-1) → ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => ∑ r : Fin (n+1) → Fin (J-1),
      (∏ i, (z (r i)-1))*orderedBinTupleLimit J (n+1) r

noncomputable def binGeneratingLimit (J : ℕ) (z : Fin (J-1) → ℝ) : ℝ :=
  ∑ h ∈ range (J+1), binDegreeLimit J z h

theorem primeGeneratingModel_bin_tendsto {J : ℕ} (hJ : 2 ≤ J)
    (z : Fin (J-1) → ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x => primeGeneratingModel (largePrimeSet x (x^((1 : ℝ)/J)))
      (primeBinWeight J z x) ⌊A*x⌋₊) atTop (𝓝 (binGeneratingLimit J z)) := by
  have hJ0 : 0 < J := by omega
  have hdegree (h : ℕ) : Tendsto (fun x => primeGeneratingDegree
      (largePrimeSet x (x^((1 : ℝ)/J))) (primeBinWeight J z x) ⌊A*x⌋₊ h)
      atTop (𝓝 (binDegreeLimit J z h)) := by
    cases h with
    | zero =>
      apply tendsto_const_nhds.congr'
      have hN := (tendsto_nat_floor_atTop.comp (tendsto_id.const_mul_atTop hA)).eventually
        (eventually_ge_atTop 1)
      filter_upwards [hN] with x hx
      change 1 ≤ ⌊A*x⌋₊ at hx
      exact (primeGeneratingDegree_zero _ _ hx).symm
    | succ n => exact primeGeneratingDegree_bin_tendsto hJ z hA n
  have ht := tendsto_finsetSum (range (J+1)) (fun h _ => hdegree h)
  apply ht.congr'
  filter_upwards [bounded_largePrimeSubsets_eventually J hJ0 A,
    eventually_gt_atTop (0 : ℝ)] with x hcard hx
  rw [allLargeBinPrimes_eq_largePrimeSet J hx.le] at hcard
  exact (primeGeneratingModel_sum_degree _ _ _ J hcard).symm

theorem primeGeneratingAverage_bin_tendsto {J : ℕ} (hJ : 2 ≤ J)
    (z : Fin (J-1) → ℝ) (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1)
    {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x => primeGeneratingAverage (largePrimeSet x (x^((1 : ℝ)/J)))
      (primeBinWeight J z x) ⌊A*x⌋₊ * (⌊A*x⌋₊ : ℝ)/(A*x)) atTop
      (𝓝 (binGeneratingLimit J z)) := by
  have herror := generating_floor_error_tendsto_zero (by omega : 0 < J) hA
    (primeBinWeight J z) (fun x p => primeBinWeight_mem_Icc J z hz x p)
  have hlim := (primeGeneratingModel_bin_tendsto hJ z hA).mul
    ((tendsto_nat_floor_div_atTop (R := ℝ)).comp (tendsto_id.const_mul_atTop hA))
  have ht := herror.add hlim
  simp only [zero_add, mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [allLargeBinPrimes_eq_largePrimeSet J hx.le]
  simp only [Function.comp_apply, id_eq]
  ring

end JointDickman

end OAI
