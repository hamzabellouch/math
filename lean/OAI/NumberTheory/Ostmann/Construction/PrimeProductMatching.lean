import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import OAI.NumberTheory.Ostmann.Construction.TransferArithmetic

namespace OAI

/-! # Equal distinct-prime products give the unique actual slot matching -/

namespace Ostmann

open scoped BigOperators Classical

theorem prime_dvd_prime_product {I : Type*} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, (p i).Prime) (q : ℕ) (hq : q.Prime)
    (hd : q ∣ ∏ i, p i) : ∃ i, q = p i := by
  obtain ⟨i, _, hi⟩ := (hq.prime.dvd_finsetProd_iff p).mp hd
  exact ⟨i, ((Nat.dvd_prime (hp i)).mp hi).resolve_left hq.ne_one⟩

theorem prime_product_matching_exists_unique {I J : Type*} [Fintype I] [Fintype J]
    (p : I → ℕ) (q : J → ℕ) (hp : ∀ i, (p i).Prime) (hq : ∀ j, (q j).Prime)
    (hinjp : Function.Injective p) (hinjq : Function.Injective q)
    (hprod : (∏ i, p i) = ∏ j, q j) : ∃! e : I ≃ J, ∀ i, p i = q (e i) := by
  have hex : ∀ i, ∃ j, p i = q j := by
    intro i
    apply prime_dvd_prime_product q hq (p i) (hp i)
    rw [← hprod]
    exact Finset.dvd_prod_of_mem p (Finset.mem_univ i)
  let f : I → J := fun i => Classical.choose (hex i)
  have hf : ∀ i, p i = q (f i) := fun i => Classical.choose_spec (hex i)
  have hfi : Function.Injective f := by
    intro i i' he
    apply hinjp
    rw [hf i, hf i', he]
  have hfs : Function.Surjective f := by
    intro j
    obtain ⟨i, hi⟩ := prime_dvd_prime_product p hp (q j) (hq j) (by
      rw [hprod]
      exact Finset.dvd_prod_of_mem q (Finset.mem_univ j))
    refine ⟨i, hinjq ?_⟩
    exact (hf i).symm.trans hi.symm
  refine ⟨Equiv.ofBijective f ⟨hfi, hfs⟩, hf, ?_⟩
  intro e he
  apply Equiv.ext
  intro i
  exact hinjq ((he i).symm.trans (hf i))

theorem prime_product_eq_iff_matching {I J : Type*} [Fintype I] [Fintype J]
    (p : I → ℕ) (q : J → ℕ) (hp : ∀ i, (p i).Prime) (hq : ∀ j, (q j).Prime)
    (hinjp : Function.Injective p) (hinjq : Function.Injective q) :
    (∏ i, p i) = (∏ j, q j) ↔ ∃! e : I ≃ J, ∀ i, p i = q (e i) := by
  constructor
  · exact prime_product_matching_exists_unique p q hp hq hinjp hinjq
  · rintro ⟨e, he, _⟩
    calc
      _ = ∏ i, q (e i) := Finset.prod_congr rfl (fun i _ => he i)
      _ = _ := e.prod_comp q

/-- Prime factors exceed the leaf frequencies, so the zero transfer numerator
has a common frequency and a unique matching of its constituent prime slots. -/
theorem diagonal_prime_matching {I J : Type*} [Fintype I] [Fintype J]
    (p : I → ℕ) (q : J → ℕ) (hp : ∀ i, (p i).Prime) (hq : ∀ j, (q j).Prime)
    (hinjp : Function.Injective p) (hinjq : Function.Injective q)
    (v w : ℤ) (hv : v ≠ 0) (hw : w ≠ 0)
    (hvp : ∀ i, v.natAbs < p i) (hwq : ∀ j, w.natAbs < q j) :
    v * (∏ j, q j : ℕ) = w * (∏ i, p i : ℕ) ↔
      v = w ∧ ∃! e : I ≃ J, ∀ i, p i = q (e i) := by
  constructor
  · intro h
    have hl : 0 < ∏ i, p i := Finset.prod_pos (fun i _ => (hp i).pos)
    have hd := diagonal_products_equal (∏ i, p i) (∏ j, q j) hl v w hv hw h
      (fun r hr hd => by obtain ⟨i, rfl⟩ := prime_dvd_prime_product p hp r hr hd; exact hvp i)
      (fun r hr hd => by obtain ⟨j, rfl⟩ := prime_dvd_prime_product q hq r hr hd; exact hwq j)
    exact ⟨hd.2, prime_product_matching_exists_unique p q hp hq hinjp hinjq hd.1⟩
  · rintro ⟨rfl, hmatch⟩
    rw [(prime_product_eq_iff_matching p q hp hq hinjp hinjq).mpr hmatch]

/-- Replacing the equal-product indicator by the sum over actual matchings
introduces no multiplicity, because all prime slots are distinct. -/
theorem prime_product_matching_sum {I J : Type*} [Fintype I] [Fintype J]
    (p : I → ℕ) (q : J → ℕ) (hp : ∀ i, (p i).Prime) (hq : ∀ j, (q j).Prime)
    (hinjp : Function.Injective p) (hinjq : Function.Injective q) (z : ℂ) :
    (if (∏ i, p i) = ∏ j, q j then z else 0) =
      ∑ e : I ≃ J, if ∀ i, p i = q (e i) then z else 0 := by
  by_cases h : (∏ i, p i) = ∏ j, q j
  · obtain ⟨e, he, hu⟩ := prime_product_matching_exists_unique p q hp hq hinjp hinjq h
    rw [ite_eq_left h, Finset.sum_eq_single e]
    · exact (ite_eq_left he).symm
    · intro e' _ hne
      rw [ite_eq_right (fun he' => hne (hu e' he'))]
    · simp
  · rw [ite_eq_right h]
    symm
    apply Finset.sum_eq_zero
    intro e _
    rw [ite_eq_right]
    intro he
    apply h
    calc
      _ = ∏ i, q (e i) := Finset.prod_congr rfl (fun i _ => he i)
      _ = _ := e.prod_comp q

end Ostmann

end OAI
