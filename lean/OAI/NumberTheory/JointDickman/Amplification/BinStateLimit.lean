import OAI.NumberTheory.JointDickman.Arithmetic.BinGeneratingLimit
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeBinProduct
import OAI.NumberTheory.JointDickman.Arithmetic.DistinctBinGenerating

namespace OAI

/-! # Existence of the unconditional finite-bin state distribution -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem distinctBinGeneratingAverage_tendsto {J : ℕ} (hJ : 2 ≤ J)
    (z : Fin (J-1) → ℝ) (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1)
    {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x => distinctBinGeneratingAverage J z A x) atTop (𝓝 (binGeneratingLimit J z)) := by
  apply (primeGeneratingAverage_bin_tendsto hJ z hz hA).congr'
  have hN := (tendsto_nat_floor_atTop.comp (tendsto_id.const_mul_atTop hA)).eventually
    (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop (1 : ℝ), distinctBinVector_val (by omega : 0 < J) A, hN] with x hx hv hn
  change 1 ≤ ⌊A*x⌋₊ at hn
  have hn0 : (⌊A*x⌋₊ : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold distinctBinGeneratingAverage primeGeneratingAverage
  have he : (∑ n ∈ Ioc 0 ⌊A*x⌋₊,
      ∏ p ∈ largePrimeSet x (x^((1 : ℝ)/J)), if p ∣ n then primeBinWeight J z x p else 1) =
      ∑ n ∈ Ioc 0 ⌊A*x⌋₊, ∏ i, z i^(distinctBinVector J x n i).val := by
    apply sum_congr rfl
    intro n hmem
    rw [primeBin_generating_product hx hJ]
    apply prod_congr rfl
    intro i hi
    rw [hv n (mem_Ioc.mp hmem).1
      ((Nat.le_floor_iff (mul_nonneg hA.le (zero_le_one.trans hx))).mp (mem_Ioc.mp hmem).2) i]
  rw [he]
  field_simp

theorem binStateGeneratingAverage_tendsto {J : ℕ} (hJ : 2 ≤ J)
    (z : Fin (J-1) → ℝ) (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1)
    {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x => binStateGeneratingAverage J z A x) atTop (𝓝 (binGeneratingLimit J z)) := by
  have ht := (binGenerating_sub_distinct_tendsto (by omega : 0 < J) z hA).add
    (distinctBinGeneratingAverage_tendsto hJ z hz hA)
  simpa only [sub_add_cancel, zero_add] using ht

theorem finiteBinStateDistribution (J : ℕ) (hJ : 2 ≤ J) :
    ∃ ν : BinCountState J → ℝ,
      (∀ r, 0 ≤ ν r) ∧ (∑ r, ν r = 1) ∧
      (∀ A : ℝ, 0 < A → ∀ r,
        Tendsto (fun x => binStateDensity J A x r) atTop (𝓝 (ν r))) := by
  apply binStateDistribution_of_generating_limits J
    (fun a => binGeneratingLimit J (fun i => interpolationNode (a i)))
  intro A hA a
  exact binStateGeneratingAverage_tendsto hJ _ (fun i => interpolationNode_mem (a i)) hA

end JointDickman

end OAI
