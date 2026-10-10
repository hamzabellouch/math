import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Tactic

namespace OAI

/-! A shifted additive fiber is bounded by the unshifted additive energy. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def minorArcValueCount {α : Type*} (S : Finset α) (f : α → ℤ) (n : ℤ) : ℕ :=
  (S.filter (fun a => f a = n)).card

lemma minor_arc_value_support {α : Type*} {S : Finset α} {f : α → ℤ} {n : ℤ}
    (hn : minorArcValueCount S f n ≠ 0) : n ∈ S.image f := by
  obtain ⟨a, ha⟩ := card_ne_zero.mp hn
  obtain ⟨haS, han⟩ := mem_filter.mp ha
  exact mem_image.mpr ⟨a, haS, han⟩

lemma minor_arc_pair_fiber {α : Type*} (S : Finset α) (f : α → ℤ) (h : ℤ) :
    ((S ×ˢ S).filter (fun v => f v.1 - f v.2 = h)).card =
      ∑ n ∈ S.image f, minorArcValueCount S f n * minorArcValueCount S f (n - h) := by
  have hfirst : ((S ×ˢ S).filter (fun v => f v.1 - f v.2 = h)).card =
      ∑ a ∈ S, minorArcValueCount S f (f a - h) := by
    simp only [card_eq_sum_ones, sum_filter, sum_product, minorArcValueCount]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    have hi : f a - f b = h ↔ f b = f a - h := by omega
    by_cases hab : f a - f b = h
    · simp only [ite_eq_left hab, ite_eq_left (hi.mp hab)]
    · simp only [ite_eq_right hab, ite_eq_right ((not_congr hi).mp hab)]
  rw [hfirst, ← sum_fiberwise_of_maps_to (fun a ha => mem_image_of_mem f ha)
    (fun a => minorArcValueCount S f (f a - h))]
  apply sum_congr rfl
  intro n _
  calc
    _ = ∑ _a ∈ S.filter (fun a => f a = n), minorArcValueCount S f (n - h) := by
      apply sum_congr rfl
      intro a ha
      rw [(mem_filter.mp ha).2]
    _ = _ := by simp only [sum_const, nsmul_eq_mul, Nat.cast_id, minorArcValueCount]

lemma minor_arc_shifted_value_squares {α : Type*} (S : Finset α) (f : α → ℤ) (h : ℤ) :
    (∑ n ∈ S.image f, minorArcValueCount S f (n - h) ^ 2) ≤
      ∑ n ∈ S.image f, minorArcValueCount S f n ^ 2 := by
  have hi : Set.InjOn (fun n : ℤ => n - h) (↑(S.image f) : Set ℤ) := by
    intro a _ b _ hab
    change a - h = b - h at hab
    omega
  rw [← sum_image (f := fun n : ℤ => minorArcValueCount S f n ^ 2) hi]
  apply sum_le_sum_of_ne_zero
  intro n _ hn
  apply minor_arc_value_support
  intro hz
  simp only [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hn
  exact hn rfl

lemma minor_arc_shifted_pair_card {α : Type*} (S : Finset α) (f : α → ℤ) (h : ℤ) :
    ((S ×ˢ S).filter (fun v => f v.1 - f v.2 = h)).card ≤
      ((S ×ˢ S).filter (fun v => f v.1 - f v.2 = 0)).card := by
  rw [minor_arc_pair_fiber, minor_arc_pair_fiber]
  simp only [sub_zero, ← pow_two]
  have he : 2 * (∑ n ∈ S.image f, minorArcValueCount S f n * minorArcValueCount S f (n - h)) ≤
      (∑ n ∈ S.image f, minorArcValueCount S f n ^ 2) +
        ∑ n ∈ S.image f, minorArcValueCount S f (n - h) ^ 2 := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro n _
    have he : (2 : ℤ) * minorArcValueCount S f n * minorArcValueCount S f (n - h) ≤
        (minorArcValueCount S f n : ℤ) ^ 2 + (minorArcValueCount S f (n - h) : ℤ) ^ 2 := by
      nlinarith [sq_nonneg ((minorArcValueCount S f n : ℤ) - minorArcValueCount S f (n - h))]
    simpa only [mul_assoc] using (show
      2 * minorArcValueCount S f n * minorArcValueCount S f (n - h) ≤
        minorArcValueCount S f n ^ 2 + minorArcValueCount S f (n - h) ^ 2 by exact_mod_cast he)
  have hs := minor_arc_shifted_value_squares S f h
  omega

/-- Every difference-of-prime-sums fiber has size at most the zero fiber. -/
theorem minor_arc_prime_shifted_fiber (P : Finset ℕ) (h : ℤ) :
    (((P ×ˢ P) ×ˢ (P ×ˢ P)).filter
      (fun v => ((v.1.1 : ℤ) + v.1.2) - ((v.2.1 : ℤ) + v.2.2) = h)).card ≤
      Finset.addEnergy P P := by
  have he := minor_arc_shifted_pair_card (P ×ˢ P)
    (fun v => (v.1 : ℤ) + v.2) h
  have hz : (((P ×ˢ P) ×ˢ (P ×ˢ P)).filter
      (fun v => ((v.1.1 : ℤ) + v.1.2) - ((v.2.1 : ℤ) + v.2.2) = 0)).card =
      Finset.addEnergy P P := by
    rw [Finset.addEnergy_eq_card_filter]
    apply congrArg Finset.card
    apply filter_congr
    intro v _
    omega
  exact hz ▸ he

end TwoPointCorrelations

end OAI
