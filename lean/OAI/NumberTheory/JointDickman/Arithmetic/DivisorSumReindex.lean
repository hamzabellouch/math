import Mathlib

namespace OAI

/-! # Reindexing a finite divisor sum over its two factors -/
namespace JointDickman
open Finset

lemma sum_Ioc_divisors_reindex {R : Type*} [AddCommMonoid R]
    (G : ℕ → ℕ → R) (X : ℕ) :
    (∑ n ∈ Ioc 0 X, ∑ d ∈ n.divisors, G d (n/d)) =
      ∑ d ∈ Ioc 0 X, ∑ k ∈ Ioc 0 (X/d), G d k := by
  have hprod : (∑ n ∈ Ioc 0 X, ∑ d ∈ n.divisors, G d (n/d)) =
      ∑ x ∈ (Ioc 0 X ×ˢ Ioc 0 X).filter (fun x => x.1*x.2 ≤ X), G x.1 x.2 := by
    calc
      _ = ∑ n ∈ Ioc 0 X, ∑ x ∈ (Ioc 0 X ×ˢ Ioc 0 X).filter
          (fun x => x.1*x.2=n), G x.1 x.2 := by
        apply sum_congr rfl
        intro n hn
        rw [←Nat.sum_divisorsAntidiagonal G,
          Nat.divisorsAntidiagonal_eq_prod_filter_of_le (mem_Ioc.mp hn).1.ne' (mem_Ioc.mp hn).2]
      _ = _ := by
        simp_rw [sum_filter]
        rw [sum_comm]
        apply sum_congr rfl
        intro x hx
        obtain ⟨hx1,hx2⟩ := mem_product.mp hx
        have hpos : 0 < x.1*x.2 := Nat.mul_pos (mem_Ioc.mp hx1).1 (mem_Ioc.mp hx2).1
        simp [hpos,eq_comm]
  rw [hprod,sum_filter,sum_product]
  apply sum_congr rfl
  intro d hd
  simp only [sum_ite,not_le,sum_const_zero,add_zero]
  congr 1
  ext k
  simp only [mem_filter,mem_Ioc]
  have hd0 := (mem_Ioc.mp hd).1
  constructor
  · rintro ⟨⟨hk0,hkX⟩,hmul⟩
    exact ⟨hk0,(Nat.le_div_iff_mul_le hd0).mpr (by simpa [mul_comm] using hmul)⟩
  · rintro ⟨hk0,hkdiv⟩
    have hmul := (Nat.le_div_iff_mul_le hd0).mp hkdiv
    exact ⟨⟨hk0,hkdiv.trans (Nat.div_le_self _ _)⟩,by simpa [mul_comm] using hmul⟩

end JointDickman

end OAI
