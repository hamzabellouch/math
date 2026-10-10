import OAI.NumberTheory.JointDickman.Amplification.BinCounts
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeTupleBounds

namespace OAI

/-! # The exact partition of the large primes into logarithmic bins -/
namespace JointDickman
open Finset

theorem primeBin_disjoint {x : ℝ} (hx : 1 ≤ x) {J k l : ℕ}
    (hJ : 0 < J) (hkl : k < l) : Disjoint (primeBin x J k) (primeBin x J l) := by
  apply disjoint_left.mpr
  intro p hp hq
  have hp' := (mem_primeBin_iff (zero_le_one.trans hx) J k p).mp hp
  have hq' := (mem_primeBin_iff (zero_le_one.trans hx) J l p).mp hq
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have he : ((k : ℝ)+1)/J ≤ (l : ℝ)/J := by
    apply div_le_div_of_nonneg_right _ hJr.le
    exact_mod_cast (Nat.succ_le_iff.mpr hkl)
  have hb := Real.rpow_le_rpow_of_exponent_le hx he
  exact (not_lt_of_ge (hp'.2.2.trans hb)) hq'.2.1

theorem largePrime_has_unique_bin {x : ℝ} (hx : 1 ≤ x) {J : ℕ} (hJ : 2 ≤ J)
    {p : ℕ} (hp : p ∈ largePrimeSet x (x^((1 : ℝ)/J))) :
    ∃! i : Fin (J-1), p ∈ primeBin x J (i.val+1) := by
  obtain ⟨hp,hlo⟩ := mem_filter.mp hp
  obtain ⟨hpx,hprime⟩ := Nat.mem_primesLE.mp hp
  have hpx' : (p : ℝ) ≤ x := (Nat.le_floor_iff (zero_le_one.trans hx)).mp hpx
  obtain ⟨k,hk,hpk⟩ := exists_higher_primeBin (zero_le_one.trans hx) (by omega : 0 < J)
    (by omega : 1 ≤ J) hprime (by simpa only [Nat.cast_one] using hlo) hpx'
  have hkl := mem_Ico.mp hk
  let i : Fin (J-1) := ⟨k-1,by omega⟩
  have hik : i.val+1 = k := by dsimp [i]; omega
  refine ⟨i,by simpa only [hik] using hpk,?_⟩
  intro j hj
  by_contra hji
  have hv : j.val ≠ i.val := fun he => hji (Fin.ext he)
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · exact (disjoint_left.mp (primeBin_disjoint hx (by omega : 0 < J) (by omega : j.val+1 < k))) hj hpk
  · exact (disjoint_left.mp (primeBin_disjoint hx (by omega : 0 < J) (by omega : k < j.val+1))) hpk hj

noncomputable def primeBinWeight (J : ℕ) (z : Fin (J-1) → ℝ) (x : ℝ) (p : ℕ) : ℝ := by
  classical
  exact ∏ i, if p ∈ primeBin x J (i.val+1) then z i else 1

theorem primeBinWeight_mem_Icc (J : ℕ) (z : Fin (J-1) → ℝ)
    (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1) (x : ℝ) (p : ℕ) :
    primeBinWeight J z x p ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  unfold primeBinWeight
  constructor
  · apply prod_nonneg
    intro i hi
    split_ifs
    · exact (hz i).1
    · exact zero_le_one
  · apply prod_le_one₀
    · intro i hi
      split_ifs
      · exact (hz i).1
      · exact zero_le_one
    · intro i hi
      split_ifs
      · exact (hz i).2
      · exact le_rfl

theorem primeBinWeight_sub_one {x : ℝ} (hx : 1 ≤ x) {J : ℕ} (hJ : 2 ≤ J)
    (z : Fin (J-1) → ℝ) {p : ℕ} (hp : p ∈ largePrimeSet x (x^((1 : ℝ)/J))) :
    primeBinWeight J z x p - 1 =
      ∑ i : Fin (J-1), if p ∈ primeBin x J (i.val+1) then z i-1 else 0 := by
  classical
  obtain ⟨i,hi,huniq⟩ := largePrime_has_unique_bin hx hJ hp
  have hnot (j : Fin (J-1)) (hji : j ≠ i) : p ∉ primeBin x J (j.val+1) :=
    fun hj => hji (huniq j hj)
  have hpw : primeBinWeight J z x p = z i := by
    unfold primeBinWeight
    rw [prod_eq_single i]
    · simp [hi]
    · intro j hj hji
      simp [hnot j hji]
    · simp
  rw [hpw, sum_eq_single i]
  · simp [hi]
  · intro j hj hji
    simp [hnot j hji]
  · simp

end JointDickman

end OAI
