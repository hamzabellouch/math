import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Two coordinates determine a triple of fixed sum. -/
theorem fixed_sum_bad_coordinate_card_le
    {α : Type*} [DecidableEq α] (T : Finset α) (B U : Finset ℕ)
    (x y z : α → ℕ) (n : ℕ)
    (hsum : ∀ t ∈ T, x t + y t + z t = n)
    (hy : ∀ t ∈ T, y t ∈ U)
    (hinj : Function.Injective (fun t => (x t, y t, z t))) :
    (T.filter (fun t => x t ∈ B)).card ≤ B.card * U.card := by
  have hcard := Finset.card_le_card_of_injOn
    (s := T.filter (fun t => x t ∈ B)) (t := B ×ˢ U)
    (fun t => (x t, y t))
    (by
      intro t ht
      obtain ⟨ht, hx⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_product.mpr ⟨hx, hy t ht⟩)
    (by
      intro a ha b hb hab
      have hax := (Finset.mem_filter.mp ha).1
      have hbx := (Finset.mem_filter.mp hb).1
      have hxy : x a = x b ∧ y a = y b := Prod.mk.inj hab
      have hz : z a = z b := by
        have := hsum a hax
        have := hsum b hbx
        omega
      apply hinj
      exact Prod.ext hxy.1 (Prod.ext hxy.2 hz))
  simpa only [Finset.card_product] using hcard

/-- A union bound for exceptional coordinates of fixed-sum triples. -/
theorem fixed_sum_bad_triples_card_le
    (T : Finset (ℕ × ℕ × ℕ)) (B U : Finset ℕ) (n : ℕ)
    (hsum : ∀ t ∈ T, t.1 + t.2.1 + t.2.2 = n)
    (hU : ∀ t ∈ T, t.1 ∈ U ∧ t.2.1 ∈ U ∧ t.2.2 ∈ U) :
    (T.filter (fun t => t.1 ∈ B ∨ t.2.1 ∈ B ∨ t.2.2 ∈ B)).card ≤
      3 * B.card * U.card := by
  have h1 : (T.filter (fun t => t.1 ∈ B)).card ≤ B.card * U.card :=
    fixed_sum_bad_coordinate_card_le T B U (fun t => t.1)
      (fun t => t.2.1) (fun t => t.2.2) n hsum
      (fun t ht => (hU t ht).2.1) (by intro a b h; exact h)
  have h2 : (T.filter (fun t => t.2.1 ∈ B)).card ≤ B.card * U.card := by
    apply fixed_sum_bad_coordinate_card_le T B U (fun t => t.2.1)
      (fun t => t.1) (fun t => t.2.2) n
    · intro t ht
      have := hsum t ht
      omega
    · intro t ht
      exact (hU t ht).1
    · intro a b h
      have hcoords := Prod.mk.inj h
      have htail := Prod.mk.inj hcoords.2
      exact Prod.ext htail.1 (Prod.ext hcoords.1 htail.2)
  have h3 : (T.filter (fun t => t.2.2 ∈ B)).card ≤ B.card * U.card := by
    apply fixed_sum_bad_coordinate_card_le T B U (fun t => t.2.2)
      (fun t => t.1) (fun t => t.2.1) n
    · intro t ht
      have := hsum t ht
      omega
    · intro t ht
      exact (hU t ht).1
    · intro a b h
      have hcoords := Prod.mk.inj h
      have htail := Prod.mk.inj hcoords.2
      exact Prod.ext htail.1 (Prod.ext htail.2 hcoords.1)
  have hfilter : T.filter (fun t => t.1 ∈ B ∨ t.2.1 ∈ B ∨ t.2.2 ∈ B) =
      (T.filter (fun t => t.1 ∈ B)) ∪
      ((T.filter (fun t => t.2.1 ∈ B)) ∪ (T.filter (fun t => t.2.2 ∈ B))) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  rw [hfilter]
  have hcard := Finset.card_union_le (T.filter (fun t => t.1 ∈ B))
    ((T.filter (fun t => t.2.1 ∈ B)) ∪ (T.filter (fun t => t.2.2 ∈ B)))
  have hcard' := Finset.card_union_le (T.filter (fun t => t.2.1 ∈ B))
    (T.filter (fun t => t.2.2 ∈ B))
  rw [Nat.mul_assoc]
  omega

/-- More triples than the exceptional union bound give a good triple. -/
theorem exists_fixed_sum_triple_avoiding
    (T : Finset (ℕ × ℕ × ℕ)) (B U : Finset ℕ) (n : ℕ)
    (hsum : ∀ t ∈ T, t.1 + t.2.1 + t.2.2 = n)
    (hU : ∀ t ∈ T, t.1 ∈ U ∧ t.2.1 ∈ U ∧ t.2.2 ∈ U)
    (hmany : 3 * B.card * U.card < T.card) :
    ∃ t ∈ T, t.1 ∉ B ∧ t.2.1 ∉ B ∧ t.2.2 ∉ B := by
  by_contra h
  have hall : ∀ t ∈ T, t.1 ∈ B ∨ t.2.1 ∈ B ∨ t.2.2 ∈ B := by
    intro t ht
    by_contra hbad
    simp only [not_or] at hbad
    exact h ⟨t, ht, hbad⟩
  have heq : T.filter (fun t => t.1 ∈ B ∨ t.2.1 ∈ B ∨ t.2.2 ∈ B) = T :=
    Finset.filter_eq_self.mpr hall
  have hbound := fixed_sum_bad_triples_card_le T B U n hsum hU
  rw [heq] at hbound
  omega

end Problem337

end

end OAI
