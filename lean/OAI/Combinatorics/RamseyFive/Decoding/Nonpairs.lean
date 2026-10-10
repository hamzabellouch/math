import Mathlib

namespace OAI

namespace SharpRamseyFive.SkewPairCounting
open scoped BigOperators
variable {I : Type*} [DecidableEq I]

def nonpairs (R : I → I → Prop) [DecidableRel R] (S : Finset I) : Finset (I × I) :=
  (S ×ˢ S).filter fun p => p.1 ≠ p.2 ∧ ¬R p.1 p.2

lemma card_nonpairs (R : I → I → Prop) [DecidableRel R] (S : Finset I) :
    (nonpairs R S).card = ∑ x ∈ S, (S.filter fun y => x ≠ y ∧ ¬R x y).card := by
  simp only [nonpairs, Finset.card_filter, Finset.sum_product]

lemma nonpairs_mono (R : I → I → Prop) [DecidableRel R] {S T : Finset I}
    (h : S ⊆ T) : nonpairs R S ⊆ nonpairs R T :=
  Finset.filter_subset_filter _ (Finset.product_subset_product h h)

lemma row_partition (R : I → I → Prop) [DecidableRel R] (hR : ∀ x, ¬R x x)
    (S : Finset I) {x : I} (hx : x ∈ S) :
    (S.filter fun y => x ≠ y ∧ ¬R x y).card + (S.filter (R x)).card + 1 = S.card := by
  have he : (S.filter fun y => ¬R x y).erase x = S.filter fun y => x ≠ y ∧ ¬R x y := by
    ext y
    simp only [Finset.mem_erase, Finset.mem_filter]
    tauto
  have hm : x ∈ S.filter fun y => ¬R x y := by simp [hx, hR x]
  have hc := Finset.card_erase_add_one hm
  rw [he] at hc
  have hp := Finset.card_filter_add_card_filter_not (s := S) (R x)
  omega

lemma sq_card_bound (R : I → I → Prop) [DecidableRel R] (hR : ∀ x, ¬R x x)
    (S : Finset I) (D : ℝ)
    (hD : ∀ x ∈ S, ((S.filter (R x)).card : ℝ) ≤ D) :
    (S.card : ℝ)^2 ≤ (nonpairs R S).card + S.card * (D+1) := by
  have hrow (x : I) (hx : x ∈ S) :
      (S.card : ℝ) ≤ (S.filter fun y => x ≠ y ∧ ¬R x y).card + (D+1) := by
    have hp : ((S.filter fun y => x ≠ y ∧ ¬R x y).card : ℝ) +
        (S.filter (R x)).card + 1 = S.card := by exact_mod_cast row_partition R hR S hx
    linarith [hD x hx]
  have hsum := Finset.sum_le_sum hrow
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_add_distrib,
    ← Nat.cast_sum, ← card_nonpairs] at hsum
  nlinarith

theorem many_nonpairs (R : I → I → Prop) [DecidableRel R]
    (hR : ∀ x, ¬R x x) (S : Finset I) (c : ℕ)
    (hc : ∀ x ∈ S, ∀ y ∈ S, R x y →
      (S.filter fun z => R x z ∧ R y z).card ≤ c)
    (hsize : 8*(c+1) ≤ S.card) :
    (S.card : ℝ)^2 ≤ 16*(nonpairs R S).card := by
  have hsz : 8*((c:ℝ)+1) ≤ S.card := by exact_mod_cast hsize
  by_cases hhigh : ∃ x ∈ S, (S.card:ℝ)/2 ≤ (S.filter (R x)).card
  · obtain ⟨x, hx, hd⟩ := hhigh
    let T := S.filter (R x)
    have hT : T ⊆ S := Finset.filter_subset _ _
    have hdeg (y : I) (hy : y ∈ T) : ((T.filter (R y)).card:ℝ) ≤ c := by
      have hy' := Finset.mem_filter.mp hy
      have he : T.filter (R y) = S.filter fun z => R x z ∧ R y z := by
        simp only [T, Finset.filter_filter]
      rw [he]
      exact_mod_cast hc x hx y hy'.1 hy'.2
    have hloc := sq_card_bound R hR T c hdeg
    have hm : ((nonpairs R T).card:ℝ) ≤ (nonpairs R S).card := by
      exact_mod_cast Finset.card_le_card (nonpairs_mono R hT)
    have hc0 : (0:ℝ) ≤ c := Nat.cast_nonneg _
    have ht0 : (0:ℝ) ≤ T.card := Nat.cast_nonneg _
    have hd' : (S.card:ℝ)/2 ≤ T.card := hd
    nlinarith [sq_nonneg ((T.card:ℝ)-(S.card:ℝ)/2),
      mul_nonneg (show 0 ≤ (T.card:ℝ)-2*((c:ℝ)+1) by linarith) ht0]
  · have hd (x : I) (hx : x ∈ S) : ((S.filter (R x)).card:ℝ) ≤ (S.card:ℝ)/2 := by
      have : ¬ (S.card:ℝ)/2 ≤ (S.filter (R x)).card := fun h => hhigh ⟨x,hx,h⟩
      exact (lt_of_not_ge this).le
    have hg := sq_card_bound R hR S ((S.card:ℝ)/2) hd
    have hn0 : (0:ℝ) ≤ (nonpairs R S).card := Nat.cast_nonneg _
    nlinarith [show (0:ℝ) ≤ c from Nat.cast_nonneg c, sq_nonneg ((S.card:ℝ)-4)]

end SharpRamseyFive.SkewPairCounting

end OAI
