import OAI.NumberTheory.TwoPoint.Fourier.MinorArcPacking
import Mathlib.NumberTheory.Harmonic.Bounds

namespace OAI

/-! Summing a truncated reciprocal over separated real representatives. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem minor_arc_packing_sum {ι : Type*} (S : Finset ι) (x w : ι → ℝ)
    (δ V R : ℝ) (hδ : 0 < δ) (hV : 0 ≤ V)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |x i - x j|)
    (hx : ∀ i ∈ S, |x i| ≤ R) (hw : ∀ i ∈ S, w i ≤ V)
    (hwinv : ∀ i ∈ S, 0 < |x i| → w i ≤ 1 / |x i|) :
    (∑ i ∈ S, w i) ≤ 2 * V + (2 / δ) * (1 + Real.log (⌈R / δ⌉₊ : ℝ)) := by
  let L := ⌈R / δ⌉₊
  let b := fun i => ⌊|x i| / δ⌋₊
  let F := fun j : ℕ => S.filter (fun i => b i = j)
  have hindex (i : ι) (hi : i ∈ S) : b i ≤ L := by
    apply Nat.floor_le_of_le
    exact (div_le_div_of_nonneg_right (hx i hi) hδ.le).trans (Nat.le_ceil _)
  have hband (j : ℕ) (i : ι) (hi : i ∈ F j) :
      (j : ℝ) * δ ≤ |x i| ∧ |x i| < (j : ℝ) * δ + δ := by
    have he : b i = j := (mem_filter.mp hi).2
    have hl := Nat.floor_le (div_nonneg (abs_nonneg (x i)) hδ.le)
    have hu := Nat.lt_floor_add_one (|x i| / δ)
    change ((b i : ℕ) : ℝ) ≤ |x i| / δ at hl
    change |x i| / δ < (b i : ℝ) + 1 at hu
    rw [he] at hl hu
    constructor
    · exact (le_div_iff₀ hδ).mp hl
    · have hh := (div_lt_iff₀ hδ).mp hu
      nlinarith
  have hcard (j : ℕ) : (F j).card ≤ 2 := by
    refine (card_le_card (s := F j) (t := S.filter (fun i =>
      (j : ℝ) * δ ≤ |x i| ∧ |x i| < (j : ℝ) * δ + δ)) ?_).trans
      (minor_arc_absolute_band_packing S x δ ((j : ℝ) * δ) hsep)
    intro i hi
    exact mem_filter.mpr ⟨(mem_filter.mp hi).1, hband j i hi⟩
  have hzero : (∑ i ∈ F 0, w i) ≤ 2 * V := by
    calc
      _ ≤ ∑ _i ∈ F 0, V := sum_le_sum (fun i hi => hw i (mem_filter.mp hi).1)
      _ = ((F 0).card : ℝ) * V := by simp
      _ ≤ 2 * V := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard 0) hV
  have hpiece (j : ℕ) (hj : j ∈ Icc 1 L) : (∑ i ∈ F j, w i) ≤ 2 / (δ * j) := by
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
    have hbound (i : ι) (hi : i ∈ F j) : w i ≤ 1 / (δ * j) := by
      have hlo := (hband j i hi).1
      have hpos : 0 < |x i| := (mul_pos hj0 hδ).trans_le hlo
      apply (hwinv i (mem_filter.mp hi).1 hpos).trans
      exact one_div_le_one_div_of_le (mul_pos hδ hj0) (by nlinarith)
    calc
      _ ≤ ∑ _i ∈ F j, 1 / (δ * j) := sum_le_sum hbound
      _ = ((F j).card : ℝ) * (1 / (δ * j)) := by simp
      _ ≤ 2 * (1 / (δ * j)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard j) (by positivity)
      _ = _ := by ring
  have hpartition : (∑ i ∈ S, w i) = ∑ j ∈ Icc 0 L, ∑ i ∈ F j, w i := by
    symm
    exact sum_fiberwise_of_maps_to (fun i hi => mem_Icc.mpr ⟨Nat.zero_le _, hindex i hi⟩) _
  have hsplit : (∑ j ∈ Icc 0 L, ∑ i ∈ F j, w i) =
      (∑ i ∈ F 0, w i) + ∑ j ∈ Icc 1 L, ∑ i ∈ F j, w i := by
    have he : Icc 0 L = insert 0 (Icc 1 L) := by
      ext j
      simp only [mem_Icc, mem_insert]
      omega
    rw [he, sum_insert (by simp)]
  have hharm : (∑ j ∈ Icc 1 L, 2 / (δ * j)) ≤
      (2 / δ) * (1 + Real.log (L : ℝ)) := by
    calc
      _ = (2 / δ) * (harmonic L : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log L) (by positivity)
  rw [hpartition, hsplit]
  exact add_le_add hzero ((sum_le_sum hpiece).trans hharm)

end TwoPointCorrelations

end OAI
