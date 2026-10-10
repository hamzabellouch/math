import OAI.NumberTheory.Ostmann.Preliminaries.SummandTails
import OAI.NumberTheory.Ostmann.Construction.SmoothPrimeMeanTest

namespace OAI

/-! # Converting full prime coverage into a nonnegative pair-weight bound -/
namespace Ostmann
open scoped Classical BigOperators

 theorem covered_weight_sum_le (P A B : Finset ℕ) (W : ℕ → ℝ)
    (hW : ∀ n, 0 ≤ W n)
    (hcover : ∀ q ∈ P, ∃ a ∈ A, ∃ b ∈ B, a + b = q) :
    (∑ q ∈ P, W q) ≤ ∑ a ∈ A, ∑ b ∈ B, W (a + b) := by
  let f : ℕ × ℕ → ℕ := fun ab => ab.1 + ab.2
  have hsub : P ⊆ (A ×ˢ B).image f := by
    intro q hq
    obtain ⟨a, ha, b, hb, h⟩ := hcover q hq
    exact Finset.mem_image.mpr ⟨(a,b), Finset.mem_product.mpr ⟨ha,hb⟩, h⟩
  calc
    _ ≤ ∑ q ∈ (A ×ˢ B).image f, W q :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hW q)
    _ ≤ ∑ ab ∈ A ×ˢ B, W (f ab) :=
      Finset.sum_image_le_of_nonneg (fun q _ => hW q)
    _ = _ := Finset.sum_product A B (fun ab => W (f ab))

 theorem smooth_covered_weight_le (P A B : Finset ℕ) (W : ℕ → ℝ) (X : ℝ)
    (hX : 1 ≤ X) (hW : ∀ n, 0 ≤ W n)
    (hP : ∀ q ∈ P, 0 < q ∧ (q : ℝ) ≤ X)
    (hcover : ∀ q ∈ P, ∃ a ∈ A, ∃ b ∈ B, a + b = q) :
    (∑ q ∈ P, Real.log q * W q * primeMeanTest (q / X)) ≤
      Real.log X * ∑ a ∈ A, ∑ b ∈ B, W (a + b) := by
  calc
    _ ≤ ∑ q ∈ P, Real.log X * W q := by
      apply Finset.sum_le_sum
      intro q hq
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (hP q hq).1
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (hP q hq).1
      calc
        _ ≤ Real.log q * W q * 1 :=
          mul_le_mul_of_nonneg_left (primeMeanTest_le_one _)
            (mul_nonneg (Real.log_nonneg hq1) (hW q))
        _ ≤ Real.log X * W q := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right (Real.log_le_log hq0 (hP q hq).2) (hW q)
    _ = Real.log X * ∑ q ∈ P, W q := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (covered_weight_sum_le P A B W hW hcover)
      (Real.log_nonneg hX)

 theorem EventuallyPrimeSumset.smooth_coverage {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N : ℕ, ∀ X : ℝ, 1 ≤ X → 2 * N ≤ X → ∀ W : ℕ → ℝ, (∀ n, 0 ≤ W n) →
      (∑ q ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime,
        Real.log q * W q * primeMeanTest (q / X)) ≤
      Real.log X * ∑ a ∈ summandPrefix A ⌊X⌋₊,
        ∑ b ∈ summandPrefix B ⌊X⌋₊, W (a + b) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro X hX hNX W hW
  let P := ((Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime).filter
    (fun q : ℕ => primeMeanTest ((q : ℝ) / X) ≠ 0)
  have hsum : (∑ q ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime,
      Real.log q * W q * primeMeanTest (q / X)) =
      ∑ q ∈ P, Real.log q * W q * primeMeanTest (q / X) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro q hq hnot
    have ht : primeMeanTest (q / X) = 0 := by simpa only [P, Finset.mem_filter, hq, true_and, not_not] using hnot
    rw [ht, mul_zero]
  rw [hsum]
  apply smooth_covered_weight_le P _ _ W X hX hW
  · intro q hq
    have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    exact ⟨(Finset.mem_Ioc.mp hh).1,
      (Nat.le_floor_iff (by linarith)).mp (Finset.mem_Ioc.mp hh).2⟩
  · intro q hq
    obtain ⟨hqP, htest⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqr, hprime⟩ := Finset.mem_filter.mp hqP
    have hqX : q ≤ ⌊X⌋₊ := (Finset.mem_Ioc.mp hqr).2
    have hmem : (q : ℝ) / X ∈ Set.Icc (5 / 8 : ℝ) (7 / 8) := by
      by_contra hout
      exact htest (primeMeanTest_zero_outside _ hout)
    have hqN : N ≤ q := by
      have hh := (le_div_iff₀ (show 0 < X by linarith)).mp hmem.1
      have : (N : ℝ) ≤ q := by linarith
      exact_mod_cast this
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sumset.mp ((hN q hqN).mpr hprime)
    exact ⟨a, (mem_summandPrefix A _ _).mpr ⟨ha, by omega⟩,
      b, (mem_summandPrefix B _ _).mpr ⟨hb, by omega⟩, hab⟩

end Ostmann

end OAI
