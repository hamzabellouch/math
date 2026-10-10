import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace OrdinarySparseRows

lemma nat_kernel_sum (S : Finset ℕ) :
    (∑ n ∈ S, (1+(n : ℝ)^2)⁻¹) ≤ 3 := by
  have ht : S ⊆ Icc 0 (max 1 (S.sup id)) := by
    intro n hn
    exact mem_Icc.mpr ⟨Nat.zero_le n, le_max_of_le_right (le_sup (f := id) hn)⟩
  apply (sum_le_sum_of_subset_of_nonneg ht (fun _ _ _ => by positivity)).trans
  let N := max 1 (S.sup id)
  have hN : 1 ≤ N := le_max_left _ _
  change (∑ n ∈ Icc 0 N, (1+(n : ℝ)^2)⁻¹) ≤ 3
  have he : Icc 0 N = Icc 0 1 ∪ Ioc 1 N := by
    ext n
    simp only [mem_Icc, mem_union, mem_Ioc]
    omega
  have hd : Disjoint (Icc 0 1 : Finset ℕ) (Ioc 1 N) := by
    apply disjoint_left.mpr
    intro n hn hm
    have := mem_Icc.mp hn
    have := mem_Ioc.mp hm
    omega
  rw [he, sum_union hd]
  have hi : (∑ n ∈ Ioc 1 N, (1+(n : ℝ)^2)⁻¹) ≤ 1 := by
    calc
      _ ≤ ∑ n ∈ Ioc 1 N, ((n : ℝ)^2)⁻¹ := by
        apply sum_le_sum
        intro n hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1.trans' (by norm_num : 0 < 1)
        exact inv_anti₀ (by positivity) (by linarith)
      _ ≤ (1 : ℝ)⁻¹-(N : ℝ)⁻¹ := by simpa using (sum_Ioc_inv_sq_le_sub (α := ℝ) (by decide) hN)
      _ ≤ 1 := by simp only [inv_one]; linarith [inv_nonneg.mpr (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hsmall : (∑ x ∈ (Icc 0 1 : Finset ℕ), (1 + (x : ℝ)^2)⁻¹) = 3/2 := by
    rw [show (Icc 0 1 : Finset ℕ) = {0,1} by decide]
    norm_num
  rw [hsmall]
  linarith

lemma floor_inj_of_separated (S : Finset ℝ) (t : ℝ)
    (hsep : (S : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|))
    (hside : ∀ s ∈ S, t ≤ s) :
    Set.InjOn (fun s => ⌊s-t⌋₊) (S : Set ℝ) := by
  intro x hx y hy he
  by_contra hne
  have hd := hsep hx hy hne
  have hx0 : 0 ≤ x-t := sub_nonneg.mpr (hside x hx)
  have hy0 : 0 ≤ y-t := sub_nonneg.mpr (hside y hy)
  have hxf := Nat.floor_le hx0
  have hyf := Nat.floor_le hy0
  have hxl := Nat.lt_floor_add_one (x-t)
  have hyl := Nat.lt_floor_add_one (y-t)
  change ⌊x-t⌋₊ = ⌊y-t⌋₊ at he
  rw [he] at hxf hxl
  have hab : |x-y| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  linarith

lemma nonneg_side_row (S : Finset ℝ) (t : ℝ)
    (hsep : (S : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|))
    (hside : ∀ s ∈ S, t ≤ s) :
    (∑ s ∈ S, (1+(s-t)^2)⁻¹) ≤ 3 := by
  classical
  calc
    _ ≤ ∑ s ∈ S, (1+((⌊s-t⌋₊ : ℕ) : ℝ)^2)⁻¹ := by
      apply sum_le_sum
      intro s hs
      have hf := Nat.floor_le (sub_nonneg.mpr (hside s hs))
      apply inv_anti₀ (by positivity)
      gcongr
    _ = ∑ n ∈ S.image (fun s => ⌊s-t⌋₊), (1+(n : ℝ)^2)⁻¹ :=
      (sum_image (f := fun n : ℕ => (1+(n : ℝ)^2)⁻¹)
        (floor_inj_of_separated S t hsep hside)).symm
    _ ≤ _ := nat_kernel_sum _

lemma separated_row (S : Finset ℝ) (t : ℝ)
    (hsep : (S : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|)) :
    (∑ s ∈ S, (1+(s-t)^2)⁻¹) ≤ 6 := by
  classical
  let Sp := S.filter (fun s => t ≤ s)
  let Sm := S.filter (fun s => ¬ t ≤ s)
  have hp : (∑ s ∈ Sp, (1+(s-t)^2)⁻¹) ≤ 3 :=
    nonneg_side_row Sp t (hsep.mono (by intro s hs; exact (mem_filter.mp hs).1))
      (by intro s hs; exact (mem_filter.mp hs).2)
  have hnegsep : ((Sm.image fun s => -s) : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|) := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
    have hab : a ≠ b := by intro he; exact hxy (congrArg Neg.neg he)
    have hh := hsep (mem_filter.mp ha).1 (mem_filter.mp hb).1 hab
    simpa only [neg_sub_neg, abs_sub_comm] using hh
  have hn := nonneg_side_row (Sm.image fun s => -s) (-t) hnegsep (by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    exact neg_le_neg (le_of_lt (lt_of_not_ge (mem_filter.mp ha).2)))
  rw [sum_image (by intro a ha b hb hab; exact neg_injective hab)] at hn
  have he : (∑ s ∈ Sm, (1+(-s- -t)^2)⁻¹) = ∑ s ∈ Sm, (1+(s-t)^2)⁻¹ := by
    apply sum_congr rfl
    intro s hs
    congr 2
    ring
  rw [he] at hn
  have hsplit := sum_filter_add_sum_filter_not S (fun s => t ≤ s) (fun s => (1+(s-t)^2)⁻¹)
  change (∑ s ∈ Sp, (1+(s-t)^2)⁻¹) + (∑ s ∈ Sm, (1+(s-t)^2)⁻¹) = _ at hsplit
  linarith

end OrdinarySparseRows

end

end OAI
