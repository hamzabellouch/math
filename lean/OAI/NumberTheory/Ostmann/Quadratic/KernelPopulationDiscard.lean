import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import OAI.NumberTheory.Ostmann.Quadratic.RootPopulations

namespace OAI

/-! # Discarding large kernels by their actual root populations -/

namespace Ostmann

open scoped BigOperators Classical

theorem nat_population_card_le_diameter (S : Finset ℕ) (D : ℕ)
    (hdiam : ∀ a ∈ S, ∀ b ∈ S, Nat.dist a b ≤ D) : S.card ≤ D + 1 := by
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    have ha : a ∈ S := Finset.min'_mem S hS
    have hsub : S ⊆ Finset.Icc a (a + D) := by
      intro b hb
      have hab : a ≤ b := Finset.min'_le S b hb
      have hd := hdiam a ha b hb
      rw [Nat.dist_eq_sub_of_le hab] at hd
      exact Finset.mem_Icc.mpr ⟨hab, by omega⟩
    have hc := Finset.card_le_card hsub
    simp only [Nat.card_Icc] at hc
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS]

theorem kernel_population_card_le (S : Finset ℤ) (root : ℤ → ℕ)
    (m D : ℕ) (hm : 0 < m) (h u : ℤ) (hu : u ≠ 0) (X : ℝ)
    (hroot : ∀ x ∈ S, u * (root x : ℤ) ^ 2 = (m : ℤ) * x - h)
    (hspan : ∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ X)
    (hD : Real.sqrt ((m : ℝ) * X / |(u : ℝ)|) ≤ D) : S.card ≤ D + 1 := by
  rw [← kernelRootPopulation_card S root m hm h u hroot]
  exact nat_population_card_le_diameter _ D
    (kernelRootPopulation_diameter S root m D h u hu X hroot hspan hD)

/-- There are at most K(D+1) points in the union of the large-kernel fibers,
where K is the number of distinct kernels. A subpower common denominator
can be retained in D, so no stronger root-count theorem is needed here. -/
theorem large_kernel_points_card_le (S : Finset ℤ) (kernel : ℤ → ℤ) (root : ℤ → ℕ)
    (m D : ℕ) (hm : 0 < m) (h : ℤ) (X H : ℝ) (hX : 0 ≤ X) (hH : 0 < H)
    (hroot : ∀ x ∈ S, kernel x * (root x : ℤ) ^ 2 = (m : ℤ) * x - h)
    (hspan : ∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ X)
    (hD : Real.sqrt ((m : ℝ) * X / H) ≤ D) :
    (S.filter (fun x => H < |(kernel x : ℝ)|)).card ≤ (S.image kernel).card * (D + 1) := by
  let R := S.filter fun x => H < |(kernel x : ℝ)|
  have hRS : R ⊆ S := Finset.filter_subset _ _
  have hfiber (u : ℤ) (hu : u ∈ R.image kernel) :
      (R.filter fun x => kernel x = u).card ≤ D + 1 := by
    obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp hu
    have hlarge : H < |(u : ℝ)| := by
      have hx' := (Finset.mem_filter.mp hx).2
      rwa [hxu] at hx'
    have hu0 : u ≠ 0 := by
      intro hu0
      simp only [hu0, Int.cast_zero, abs_zero] at hlarge
      linarith
    apply kernel_population_card_le _ root m D hm h u hu0 X
    · intro y hy
      obtain ⟨hyR, heq⟩ := Finset.mem_filter.mp hy
      simpa only [heq] using hroot y (hRS hyR)
    · intro y hy z hz
      exact hspan y (hRS (Finset.mem_filter.mp hy).1) z (hRS (Finset.mem_filter.mp hz).1)
    · apply (Real.sqrt_le_sqrt ?_).trans hD
      exact div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg m) hX) hH hlarge.le
  have hcount : R.card ≤ (R.image kernel).card * (D + 1) := by
    rw [Finset.card_eq_sum_card_image kernel R]
    simpa using Finset.sum_le_card_nsmul (R.image kernel)
      (fun u => (R.filter fun x => kernel x = u).card) (D + 1) hfiber
  exact hcount.trans (Nat.mul_le_mul_right (D + 1)
    (Finset.card_le_card (Finset.image_subset_image hRS)))

end Ostmann

end OAI
