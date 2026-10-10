import OAI.NumberTheory.JointDickman.Amplification.BinMarginalGenerating
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeDegreeRestriction

namespace OAI

/-! # High-bin avoidance is precisely a prime cutoff -/
namespace JointDickman
open Finset

 theorem highBinPrimeWeight {J k : ℕ} (hJ : 2 ≤ J) {x : ℝ} (hx : 1 ≤ x)
    {p : ℕ} (hp : p ∈ largePrimeSet x (x^((1 : ℝ)/J))) :
    primeBinWeight J (highBinZeroWeight J k) x p =
      if x^((k : ℝ)/J) < p then 0 else 1 := by
  classical
  obtain ⟨i,hi,huniq⟩ := largePrime_has_unique_bin hx hJ hp
  have hw : primeBinWeight J (highBinZeroWeight J k) x p = highBinZeroWeight J k i := by
    unfold primeBinWeight
    rw [prod_eq_single i]
    · simp [hi]
    · intro j _ hji
      have hj : p ∉ primeBin x J (j.val+1) := fun hj => hji (huniq j hj)
      simp [hj]
    · simp
  rw [hw, highBinZeroWeight]
  obtain ⟨_,hpl,hpu⟩ := (mem_primeBin_iff (zero_le_one.trans hx) J (i.val+1) p).mp hi
  have hJr : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have he : k ≤ i.val+1 ↔ x^((k : ℝ)/J) < p := by
    constructor
    · intro hki
      have hh : (k : ℝ)/J ≤ (i.val+1 : ℕ)/J :=
        div_le_div_of_nonneg_right (by exact_mod_cast hki) hJr.le
      exact (Real.rpow_le_rpow_of_exponent_le hx hh).trans_lt hpl
    · intro hkp
      by_contra hk
      have hh : (((i.val+1 : ℕ) : ℝ)+1)/J ≤ (k : ℝ)/J := by
        apply div_le_div_of_nonneg_right _ hJr.le
        exact_mod_cast (show i.val+1+1 ≤ k by omega)
      exact (not_lt_of_ge (hpu.trans (Real.rpow_le_rpow_of_exponent_le hx hh))) hkp
  simp only [he]

 theorem largePrimeSet_cutoff_subset {J k : ℕ} (_hJ : 0 < J) (hk : 0 < k)
    {x : ℝ} (hx : 1 ≤ x) :
    largePrimeSet x (x^((k : ℝ)/J)) ⊆ largePrimeSet x (x^((1 : ℝ)/J)) := by
  have hr : (1 : ℝ)/J ≤ (k : ℝ)/J := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg J)
    exact_mod_cast hk
  intro p hp
  obtain ⟨hp,hpc⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hp,(Real.rpow_le_rpow_of_exponent_le hx hr).trans_lt hpc⟩

 theorem highBinPrimeDegree {J k : ℕ} (hJ : 2 ≤ J) (hk : 0 < k) {x : ℝ} (hx : 1 ≤ x)
    (N h : ℕ) :
    primeGeneratingDegree (largePrimeSet x (x^((1 : ℝ)/J)))
      (primeBinWeight J (highBinZeroWeight J k) x) N h =
    primeGeneratingDegree (largePrimeSet x (x^((k : ℝ)/J))) (fun _ => 0) N h := by
  have hsub := largePrimeSet_cutoff_subset (by omega : 0 < J) hk hx
  rw [primeGeneratingDegree_restrict _ _ hsub]
  · apply primeGeneratingDegree_congr
    intro p hp
    rw [highBinPrimeWeight hJ hx (hsub hp)]
    exact ite_eq_left (mem_filter.mp hp).2
  · intro p hp hpQ
    rw [highBinPrimeWeight hJ hx hp]
    apply ite_eq_right
    intro hpc
    exact hpQ (mem_filter.mpr ⟨(mem_filter.mp hp).1,hpc⟩)

end JointDickman

end OAI
