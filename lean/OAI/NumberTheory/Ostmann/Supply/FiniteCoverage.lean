import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators

def smallElements (A : Finset ℕ) (r : ℕ) : Finset ℕ := A.filter (· ≤ r)

def largeElements (A : Finset ℕ) (r : ℕ) : Finset ℕ := A.filter (r < ·)

def boundarySums (A B : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (((smallElements A r).product B).image (fun ab => ab.1 + ab.2)) ∪
    ((A.product (smallElements B r)).image (fun ab => ab.1 + ab.2))

def exceptionalCovered (A B P : Finset ℕ) (r : ℕ) : Finset ℕ :=
  P ∩ boundarySums A B r

@[simp] theorem mem_smallElements {A : Finset ℕ} {r a : ℕ} :
    a ∈ smallElements A r ↔ a ∈ A ∧ a ≤ r := Finset.mem_filter

@[simp] theorem mem_largeElements {A : Finset ℕ} {r a : ℕ} :
    a ∈ largeElements A r ↔ a ∈ A ∧ r < a := Finset.mem_filter

theorem exists_injective_representatives (A B P : Finset ℕ)
    (hcover : ∀ p ∈ P, ∃ a ∈ A, ∃ b ∈ B, a + b = p) :
    ∃ e : ℕ → ℕ × ℕ, Set.InjOn e (P : Set ℕ) ∧
      ∀ p ∈ P, e p ∈ A.product B ∧ (e p).1 + (e p).2 = p := by
  classical
  have hrep : ∀ p : ℕ, ∃ ab : ℕ × ℕ,
      p ∈ P → ab ∈ A.product B ∧ ab.1 + ab.2 = p := by
    intro p
    by_cases hp : p ∈ P
    · obtain ⟨a, ha, b, hb, hab⟩ := hcover p hp
      exact ⟨(a, b), fun _ => ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩⟩
    · exact ⟨(0, 0), fun hp' => (hp hp').elim⟩
  choose e he using hrep
  refine ⟨e, ?_, he⟩
  intro p hp q hq hpq
  calc
    p = (e p).1 + (e p).2 := (he p hp).2.symm
    _ = (e q).1 + (e q).2 := by rw [hpq]
    _ = q := (he q hq).2

theorem weighted_coverage (A B P : Finset ℕ) (W : ℕ → ℝ)
    (hW : ∀ n, 0 ≤ W n)
    (hcover : ∀ p ∈ P, ∃ a ∈ A, ∃ b ∈ B, a + b = p) :
    ∑ p ∈ P, W p ≤ ∑ a ∈ A, ∑ b ∈ B, W (a + b) := by
  classical
  obtain ⟨e, he, hrep⟩ := exists_injective_representatives A B P hcover
  have hsum : ∑ p ∈ P, W p ≤ ∑ ab ∈ A.product B, W (ab.1 + ab.2) := by
    apply Finset.sum_le_sum_of_injOn e he
    · intro ab hab
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hab
      exact (hrep p hp).1
    · intro p hp
      exact le_of_eq (congrArg W (hrep p hp).2.symm)
    · intro ab _ _
      exact hW _
  simpa only [Finset.product_eq_sprod, Finset.sum_product] using hsum

@[simp] theorem mem_boundarySums {A B : Finset ℕ} {r p : ℕ} :
    p ∈ boundarySums A B r ↔
      ∃ a ∈ A, ∃ b ∈ B, a + b = p ∧ (a ≤ r ∨ b ≤ r) := by
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp hp
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      exact ⟨a, (mem_smallElements.mp ha).1, b, hb, heq,
        Or.inl (mem_smallElements.mp ha).2⟩
    · obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp hp
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      exact ⟨a, ha, b, (mem_smallElements.mp hb).1, heq,
        Or.inr (mem_smallElements.mp hb).2⟩
  · rintro ⟨a, ha, b, hb, heq, hsmall⟩
    rcases hsmall with ha' | hb'
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
        ⟨(a, b), Finset.mem_product.mpr ⟨mem_smallElements.mpr ⟨ha, ha'⟩, hb⟩, heq⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
        ⟨(a, b), Finset.mem_product.mpr ⟨ha, mem_smallElements.mpr ⟨hb, hb'⟩⟩, heq⟩))

theorem card_boundarySums_le (A B : Finset ℕ) (r : ℕ) :
    (boundarySums A B r).card ≤
      (smallElements A r).card * B.card + A.card * (smallElements B r).card := by
  calc
    (boundarySums A B r).card ≤
        (((smallElements A r).product B).image (fun ab => ab.1 + ab.2)).card +
        ((A.product (smallElements B r)).image (fun ab => ab.1 + ab.2)).card :=
      Finset.card_union_le _ _
    _ ≤ ((smallElements A r).product B).card + (A.product (smallElements B r)).card :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = _ := by simp only [Finset.product_eq_sprod, Finset.card_product]

theorem exceptionalCovered_subset (A B P : Finset ℕ) (r : ℕ) :
    exceptionalCovered A B P r ⊆ P := Finset.inter_subset_left

theorem card_exceptionalCovered_le (A B P : Finset ℕ) (r : ℕ) :
    (exceptionalCovered A B P r).card ≤
      (smallElements A r).card * B.card + A.card * (smallElements B r).card :=
  (Finset.card_le_card Finset.inter_subset_right).trans (card_boundarySums_le A B r)

theorem large_representation_of_not_exceptional (A B P : Finset ℕ) (r p : ℕ)
    (hcover : ∀ p ∈ P, ∃ a ∈ A, ∃ b ∈ B, a + b = p)
    (hp : p ∈ P \ exceptionalCovered A B P r) :
    ∃ a ∈ largeElements A r, ∃ b ∈ largeElements B r, a + b = p := by
  obtain ⟨hpP, hpE⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨a, ha, b, hb, hab⟩ := hcover p hpP
  have hnsmall : ¬ (a ≤ r ∨ b ≤ r) := by
    intro hsmall
    exact hpE (Finset.mem_inter.mpr
      ⟨hpP, mem_boundarySums.mpr ⟨a, ha, b, hb, hab, hsmall⟩⟩)
  refine ⟨a, mem_largeElements.mpr ⟨ha, ?_⟩,
    b, mem_largeElements.mpr ⟨hb, ?_⟩, hab⟩
  · exact Nat.lt_of_not_ge (fun h => hnsmall (Or.inl h))
  · exact Nat.lt_of_not_ge (fun h => hnsmall (Or.inr h))

theorem weighted_large_coverage (A B P : Finset ℕ) (r : ℕ) (W : ℕ → ℝ)
    (hW : ∀ n, 0 ≤ W n)
    (hcover : ∀ p ∈ P, ∃ a ∈ A, ∃ b ∈ B, a + b = p) :
    ∑ p ∈ P \ exceptionalCovered A B P r, W p ≤
      ∑ a ∈ largeElements A r, ∑ b ∈ largeElements B r, W (a + b) :=
  weighted_coverage _ _ _ W hW (large_representation_of_not_exceptional A B P r · hcover)

theorem weighted_coverage_with_boundary_loss (A B P : Finset ℕ) (r : ℕ)
    (W : ℕ → ℝ) (M : ℝ) (hW : ∀ n, 0 ≤ W n) (hM : 0 ≤ M)
    (hWM : ∀ p ∈ P, W p ≤ M)
    (hcover : ∀ p ∈ P, ∃ a ∈ A, ∃ b ∈ B, a + b = p) :
    ∑ p ∈ P, W p ≤
      (∑ a ∈ largeElements A r, ∑ b ∈ largeElements B r, W (a + b)) +
      ((smallElements A r).card * B.card + A.card * (smallElements B r).card : ℕ) * M := by
  have htail := weighted_large_coverage A B P r W hW hcover
  have hbad : ∑ p ∈ exceptionalCovered A B P r, W p ≤
      (exceptionalCovered A B P r).card * M := by
    calc
      ∑ p ∈ exceptionalCovered A B P r, W p ≤ ∑ _p ∈ exceptionalCovered A B P r, M :=
        Finset.sum_le_sum (fun p hp => hWM p (exceptionalCovered_subset A B P r hp))
      _ = _ := by simp
  have hcard : ((exceptionalCovered A B P r).card : ℝ) ≤
      ((smallElements A r).card * B.card + A.card * (smallElements B r).card : ℕ) := by
    exact_mod_cast card_exceptionalCovered_le A B P r
  have hsplit := Finset.sum_sdiff (f := W) (exceptionalCovered_subset A B P r)
  have hbad' := hbad.trans (mul_le_mul_of_nonneg_right hcard hM)
  linarith

def primesInInterval (L U : ℕ) : Finset ℕ := (Finset.Icc L U).filter Nat.Prime

@[simp] theorem mem_primesInInterval {L U p : ℕ} :
    p ∈ primesInInterval L U ↔ L ≤ p ∧ p ≤ U ∧ Nat.Prime p := by
  simp only [primesInInterval, Finset.mem_filter, Finset.mem_Icc, and_assoc]

theorem weighted_prime_interval_coverage (A B : Finset ℕ) (L U : ℕ) (W : ℕ → ℝ)
    (hW : ∀ n, 0 ≤ W n)
    (hcover : ∀ p, Nat.Prime p → L ≤ p → p ≤ U →
      ∃ a ∈ A, ∃ b ∈ B, a + b = p) :
    ∑ p ∈ primesInInterval L U, W p ≤ ∑ a ∈ A, ∑ b ∈ B, W (a + b) := by
  apply weighted_coverage A B _ W hW
  intro p hp
  obtain ⟨hpL, hpU, hprime⟩ := mem_primesInInterval.mp hp
  exact hcover p hprime hpL hpU

end Ostmann.Supply

end

end OAI
