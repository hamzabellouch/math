import OAI.NumberTheory.JointDickman.Amplification.GeneratingDegreeExpansion
import OAI.NumberTheory.JointDickman.Amplification.OrderedBinTuples

namespace OAI

/-! # The generating polynomial in terms of ordered bin tuples -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology

open Classical in
theorem primeBinWeight_tuple_expansion {x : ℝ} (hx : 1 ≤ x) {J : ℕ} (hJ : 2 ≤ J)
    (z : Fin (J-1) → ℝ) {h : ℕ} (v : Fin h → ℕ)
    (hv : ∀ i, v i ∈ largePrimeSet x (x^((1 : ℝ)/J))) :
    (∏ i, (primeBinWeight J z x (v i)-1)) =
      ∑ r : Fin h → Fin (J-1),
        if ∀ i, v i ∈ primeBin x J ((r i).val+1) then ∏ i, (z (r i)-1) else 0 := by
  calc
    _ = ∏ i : Fin h, ∑ j : Fin (J-1),
        if v i ∈ primeBin x J (j.val+1) then z j-1 else 0 := by
      exact prod_congr rfl (fun i _ => primeBinWeight_sub_one hx hJ z (hv i))
    _ = ∑ r : Fin h → Fin (J-1),
        ∏ i, if v i ∈ primeBin x J ((r i).val+1) then z (r i)-1 else 0 :=
      Fintype.prod_sum _
    _ = _ := by
      apply sum_congr rfl
      intro r hr
      rw [Fintype.prod_ite_zero]
      split_ifs <;> rfl

theorem primeGeneratingDegree_binExpansion {x A : ℝ} (hx : 1 ≤ x) {J : ℕ} (hJ : 2 ≤ J)
    (z : Fin (J-1) → ℝ) (h : ℕ) :
    primeGeneratingDegree (largePrimeSet x (x^((1 : ℝ)/J))) (primeBinWeight J z x) ⌊A*x⌋₊ h =
      ∑ r : Fin h → Fin (J-1), (∏ i, (z (r i)-1)) * orderedBinTupleMass J h A x r := by
  classical
  rw [primeGeneratingDegree_ordered]
  calc
    _ = ∑ v ∈ orderedPrimeTuples (largePrimeSet x (x^((1 : ℝ)/J))) h,
        ∑ r : Fin h → Fin (J-1), (∏ i, (z (r i)-1)) *
          (if (∀ i, v i ∈ primeBin x J ((r i).val+1)) ∧ (∏ i, v i) ≤ ⌊A*x⌋₊
            then ∏ i, 1/(v i : ℝ) else 0) := by
      apply sum_congr rfl
      intro v hv
      rw [primeBinWeight_tuple_expansion hx hJ z v (orderedPrimeTuples_mem.mp hv).1]
      have hd : ((∏ i, v i : ℕ) : ℝ) = ∏ i, (v i : ℝ) := by norm_cast
      rw [hd]
      by_cases hprod : (∏ i, v i) ≤ ⌊A*x⌋₊
      · simp only [hprod, ite_true, and_true, sum_div]
        apply sum_congr rfl
        intro r hr
        by_cases hb : ∀ i, v i ∈ primeBin x J ((r i).val+1)
        · simp [hb, prod_inv_distrib, div_eq_mul_inv]
        · simp [hb]
      · simp [hprod]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro r hr
      rw [orderedBinTupleMass, mul_sum]

theorem primeGeneratingDegree_bin_tendsto {J : ℕ} (hJ : 2 ≤ J)
    (z : Fin (J-1) → ℝ) {A : ℝ} (hA : 0 < A) (n : ℕ) :
    Tendsto (fun x => primeGeneratingDegree (largePrimeSet x (x^((1 : ℝ)/J)))
      (primeBinWeight J z x) ⌊A*x⌋₊ (n+1)) atTop
      (𝓝 (∑ r : Fin (n+1) → Fin (J-1), (∏ i, (z (r i)-1))*orderedBinTupleLimit J (n+1) r)) := by
  have ht := tendsto_finsetSum univ (fun r _ =>
    (orderedBinTupleMass_tendsto hJ hA n r).const_mul (∏ i, (z (r i)-1)))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact (primeGeneratingDegree_binExpansion hx hJ z (n+1)).symm

end JointDickman

end OAI
