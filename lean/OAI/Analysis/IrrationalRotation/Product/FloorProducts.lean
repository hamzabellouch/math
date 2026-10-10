import OAI.Analysis.IrrationalRotation.Rotation.FloorCocycle
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

namespace Invariant233.FloorProducts

open scoped BigOperators

theorem finite_cocycle {ι : Type*} (s : Finset ι) (c x θ : ι → ℝ) (k n : ℤ) :
    Real.exp (-(∑ i ∈ s, c i * (⌊x i + ((k + n : ℤ) : ℝ) * θ i⌋ : ℝ))) =
      Real.exp (-(∑ i ∈ s,
        c i * (⌊Int.fract (x i + (k : ℝ) * θ i) + (n : ℝ) * θ i⌋ : ℝ))) *
      Real.exp (-(∑ i ∈ s, c i * (⌊x i + (k : ℝ) * θ i⌋ : ℝ))) := by
  have hsum : (∑ i ∈ s, c i * (⌊x i + ((k + n : ℤ) : ℝ) * θ i⌋ : ℝ)) =
      (∑ i ∈ s, c i * (⌊x i + (k : ℝ) * θ i⌋ : ℝ)) +
      ∑ i ∈ s, c i * (⌊Int.fract (x i + (k : ℝ) * θ i) + (n : ℝ) * θ i⌋ : ℝ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← FloorCocycle.floor_cocycle, Int.cast_add, mul_add]
  rw [hsum, neg_add, Real.exp_add, mul_comm]

theorem finite_cocycle_zero {ι : Type*} (s : Finset ι) (c x : ι → ℝ)
    (hx : ∀ i ∈ s, x i ∈ Set.Ico (0 : ℝ) 1) :
    Real.exp (-(∑ i ∈ s, c i * (⌊x i⌋ : ℝ))) = 1 := by
  have hsum : (∑ i ∈ s, c i * (⌊x i⌋ : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Int.floor_eq_zero_iff.mpr (hx i hi)]
    simp
  rw [hsum, neg_zero, Real.exp_zero]

theorem finite_cocycle_antitone {ι : Type*} (s : Finset ι) (c x θ : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hθ : ∀ i ∈ s, 0 ≤ θ i) :
    Antitone (fun k : ℤ => Real.exp (-(∑ i ∈ s,
      c i * (⌊x i + (k : ℝ) * θ i⌋ : ℝ)))) := by
  intro k n hkn
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hc i hi)
  have hkn' : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
  have harg : x i + (k : ℝ) * θ i ≤ x i + (n : ℝ) * θ i := by
    nlinarith [hθ i hi]
  exact_mod_cast Int.floor_mono harg

theorem finite_ratio_eq {ι : Type*} (s : Finset ι) (c x y t : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hxy : ∀ i ∈ s, x i ≤ y i)
    (hy : ∀ i ∈ s, y i < 1) :
    Real.exp (-(∑ i ∈ s, c i * (⌊y i + t i⌋ : ℝ))) /
        Real.exp (-(∑ i ∈ s, c i * (⌊x i + t i⌋ : ℝ))) =
      Real.exp (-(∑ i ∈ s,
        if x i < 1 - Int.fract (t i) ∧ 1 - Int.fract (t i) ≤ y i then c i else 0)) := by
  rw [← Real.exp_sub]
  congr 1
  have hsum : (∑ i ∈ s, c i * (⌊y i + t i⌋ : ℝ)) -
      (∑ i ∈ s, c i * (⌊x i + t i⌋ : ℝ)) =
      ∑ i ∈ s, if x i < 1 - Int.fract (t i) ∧ 1 - Int.fract (t i) ≤ y i
        then c i else 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_sub]
    have hd := FloorCocycle.floor_sub_eq_crossing (hx i hi)
      (lt_of_le_of_lt (hxy i hi) (hy i hi)) (le_trans (hx i hi) (hxy i hi))
      (hy i hi) (hxy i hi) (t i)
    have hd' : (⌊y i + t i⌋ : ℝ) - (⌊x i + t i⌋ : ℝ) =
        if x i < 1 - Int.fract (t i) ∧ 1 - Int.fract (t i) ≤ y i then 1 else 0 := by
      exact_mod_cast hd
    rw [hd']
    split_ifs <;> simp
  linarith

theorem finite_ratio_suppression {ι : Type*} (s a : Finset ι) (c x y t : ι → ℝ)
    (ha : a ⊆ s) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hxy : ∀ i ∈ s, x i ≤ y i)
    (hy : ∀ i ∈ s, y i < 1)
    (hcross : ∀ i ∈ a, x i < 1 - Int.fract (t i) ∧ 1 - Int.fract (t i) ≤ y i) :
    Real.exp (-(∑ i ∈ s, c i * (⌊y i + t i⌋ : ℝ))) /
        Real.exp (-(∑ i ∈ s, c i * (⌊x i + t i⌋ : ℝ))) ≤
      Real.exp (-(∑ i ∈ a, c i)) := by
  classical
  rw [finite_ratio_eq s c x y t hx hxy hy]
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  have heq : (∑ i ∈ a, c i) = ∑ i ∈ a,
      if x i < 1 - Int.fract (t i) ∧ 1 - Int.fract (t i) ≤ y i then c i else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [ite_eq_left (hcross i hi)]
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg ha
  intro i hi hia
  split_ifs
  · exact hc i hi
  · exact le_rfl

theorem finite_ratio_le_one {ι : Type*} (s : Finset ι) (c x y t : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hx : ∀ i ∈ s, 0 ≤ x i)
    (hxy : ∀ i ∈ s, x i ≤ y i) (hy : ∀ i ∈ s, y i < 1) :
    Real.exp (-(∑ i ∈ s, c i * (⌊y i + t i⌋ : ℝ))) /
        Real.exp (-(∑ i ∈ s, c i * (⌊x i + t i⌋ : ℝ))) ≤ 1 := by
  simpa using finite_ratio_suppression s ∅ c x y t (Finset.empty_subset s)
    hc hx hxy hy (by simp)

theorem finite_ratio_le_exp_neg_cost {ι : Type*} (s : Finset ι) (c x y t : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hx : ∀ i ∈ s, 0 ≤ x i)
    (hxy : ∀ i ∈ s, x i ≤ y i) (hy : ∀ i ∈ s, y i < 1)
    (i : ι) (hi : i ∈ s)
    (hcross : x i < 1 - Int.fract (t i) ∧ 1 - Int.fract (t i) ≤ y i) :
    Real.exp (-(∑ j ∈ s, c j * (⌊y j + t j⌋ : ℝ))) /
        Real.exp (-(∑ j ∈ s, c j * (⌊x j + t j⌋ : ℝ))) ≤ Real.exp (-c i) := by
  classical
  simpa using finite_ratio_suppression s {i} c x y t
    (Finset.singleton_subset_iff.mpr hi) hc hx hxy hy (by simpa using hcross)

theorem finite_ratio_cap {ι : Type*} (s a : Finset ι) (c x y t : ι → ℝ)
    (ha : a ⊆ s) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hx : ∀ i ∈ s, x i ∈ Set.Ico (0 : ℝ) 1)
    (hy : ∀ i ∈ s, y i ∈ Set.Ico (0 : ℝ) 1)
    (hxy : ∀ i ∈ s, i ∉ a → x i ≤ y i) :
    Real.exp (-(∑ i ∈ s, c i * (⌊y i + t i⌋ : ℝ))) /
        Real.exp (-(∑ i ∈ s, c i * (⌊x i + t i⌋ : ℝ))) ≤
      Real.exp (∑ i ∈ a, c i) := by
  classical
  rw [← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have hsum : (∑ i ∈ s, c i * (⌊x i + t i⌋ : ℝ)) -
      (∑ i ∈ s, c i * (⌊y i + t i⌋ : ℝ)) ≤ ∑ i ∈ a, c i := by
    rw [← Finset.sum_sub_distrib]
    have heq : (∑ i ∈ a, c i) = ∑ i ∈ s, if i ∈ a then c i else 0 := by
      calc
        _ = ∑ i ∈ a, if i ∈ a then c i else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [ite_eq_left hi]
        _ = ∑ i ∈ s, if i ∈ a then c i else 0 := by
          apply Finset.sum_subset ha
          intro i his hia
          rw [ite_eq_right hia]
    rw [heq]
    apply Finset.sum_le_sum
    intro i hi
    by_cases hia : i ∈ a
    · rw [ite_eq_left hia]
      have hf := (FloorCocycle.floor_sub_bounds (hy i hi).1 (hy i hi).2
        (hx i hi).1 (hx i hi).2 (t i)).2
      have hf' : (⌊x i + t i⌋ : ℝ) - (⌊y i + t i⌋ : ℝ) ≤ 1 := by
        exact_mod_cast hf
      calc
        _ = c i * ((⌊x i + t i⌋ : ℝ) - (⌊y i + t i⌋ : ℝ)) := by ring
        _ ≤ c i * 1 := mul_le_mul_of_nonneg_left hf' (hc i hi)
        _ = c i := mul_one _
    · rw [ite_eq_right hia]
      have hf : (⌊x i + t i⌋ : ℝ) ≤ (⌊y i + t i⌋ : ℝ) := by
        exact_mod_cast Int.floor_mono (show x i + t i ≤ y i + t i by
          linarith [hxy i hi hia])
      exact sub_nonpos.mpr (mul_le_mul_of_nonneg_left hf (hc i hi))
  linarith

end Invariant233.FloorProducts

end OAI
