import OAI.NumberTheory.JointDickman.Arithmetic.PrimeBinPartition
import OAI.NumberTheory.JointDickman.Arithmetic.RepeatedPrimeDensity

namespace OAI

/-! # Prime generating weights as products of bin counts -/
namespace JointDickman
open Finset

theorem generating_product_bins {ι : Type*} [Fintype ι] (P : Finset ℕ)
    (E : ι → Finset ℕ) (hE : ∀ i, E i ⊆ P) (z : ι → ℝ) (n : ℕ) :
    (∏ p ∈ P, if p ∣ n then ∏ i, (if p ∈ E i then z i else 1) else 1) =
      ∏ i, z i ^ distinctBinCount (E i) n := by
  classical
  calc
    _ = ∏ p ∈ P, ∏ i, if p ∈ E i ∧ p ∣ n then z i else 1 := by
      apply prod_congr rfl
      intro p hp
      by_cases hpn : p ∣ n <;> simp [hpn]
    _ = ∏ i, ∏ p ∈ P, if p ∈ E i ∧ p ∣ n then z i else 1 := prod_comm
    _ = _ := by
      apply prod_congr rfl
      intro i hi
      rw [← prod_filter]
      have he : P.filter (fun p => p ∈ E i ∧ p ∣ n) = (E i).filter (fun p => p ∣ n) := by
        ext p
        simp only [mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hE i h.1,h⟩⟩
      rw [he]
      exact prod_const _

theorem primeBin_subset_largePrimeSet {x : ℝ} (hx : 1 ≤ x) {J : ℕ} (hJ : 2 ≤ J)
    (i : Fin (J-1)) : primeBin x J (i.val+1) ⊆ largePrimeSet x (x^((1 : ℝ)/J)) := by
  intro p hp
  obtain ⟨hprime,hpl,hpu⟩ := (mem_primeBin_iff (zero_le_one.trans hx) J (i.val+1) p).mp hp
  have hJr : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hl : (1 : ℝ)/J ≤ ((i.val+1 : ℕ) : ℝ)/J := by
    apply div_le_div_of_nonneg_right _ hJr.le
    exact_mod_cast (show 1 ≤ i.val+1 by omega)
  have hu : (((i.val+1 : ℕ) : ℝ)+1)/J ≤ 1 := by
    apply (div_le_one hJr).mpr
    have hi := i.isLt
    exact_mod_cast (show i.val+1+1 ≤ J by omega)
  apply mem_filter.mpr
  refine ⟨Nat.mem_primesLE.mpr ⟨?_,hprime⟩, ?_⟩
  · apply Nat.le_floor
    exact hpu.trans (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx hu)
  · exact (Real.rpow_le_rpow_of_exponent_le hx hl).trans_lt hpl

theorem primeBin_generating_product {x : ℝ} (hx : 1 ≤ x) {J : ℕ} (hJ : 2 ≤ J)
    (z : Fin (J-1) → ℝ) (n : ℕ) :
    (∏ p ∈ largePrimeSet x (x^((1 : ℝ)/J)), if p ∣ n then primeBinWeight J z x p else 1) =
      ∏ i : Fin (J-1), z i ^ distinctBinCount (primeBin x J (i.val+1)) n :=
  generating_product_bins _ _ (primeBin_subset_largePrimeSet hx hJ) z n

end JointDickman

end OAI
