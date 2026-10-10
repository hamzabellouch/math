import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

universe uIndex

namespace QuantitativeVanDerWaerden

open scoped BigOperators

abbrev Vec (D : ℕ) := Fin D → ℝ

def normSq {D : ℕ} (x : Vec D) : ℝ := ∑ i, (x i) ^ 2

def distSq {D : ℕ} (x y : Vec D) : ℝ := ∑ i, (x i - y i) ^ 2

theorem normSq_nonneg {D : ℕ} (x : Vec D) : 0 ≤ normSq x :=
  Finset.sum_nonneg fun i _ => sq_nonneg (x i)

/-- On either nonnegative ray, squared separation is strictly less than
the width of a common half-open quadratic band. -/
theorem weighted_nonneg_band_sq_dist_lt_one (a C m x y : ℝ)
    (ha : 0 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxb : m ≤ a * x ^ 2 + C ∧ a * x ^ 2 + C < m + 1)
    (hyb : m ≤ a * y ^ 2 + C ∧ a * y ^ 2 + C < m + 1) :
    a * (x - y) ^ 2 < 1 := by
  by_cases hxy : x ≤ y
  · have hprod : 0 ≤ a * x * (y - x) :=
      mul_nonneg (mul_nonneg ha hx) (sub_nonneg.mpr hxy)
    nlinarith [hxb.1, hyb.2]
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hprod : 0 ≤ a * y * (x - y) :=
      mul_nonneg (mul_nonneg ha hy) (sub_nonneg.mpr hyx)
    nlinarith [hyb.1, hxb.2]

/-- Weighted scalar packing, including the zero quadratic coefficient.
The parameters may have either sign, and the finite index type is arbitrary. -/
theorem weighted_scalar_band_card_le_two {ι : Type uIndex} (s : Finset ι)
    (t : ι → ℝ) (a C m : ℝ) (ha : 0 ≤ a)
    (hsep : (s : Set ι).Pairwise fun i j => 1 ≤ a * (t i - t j) ^ 2)
    (hband : ∀ i ∈ s, m ≤ a * (t i) ^ 2 + C ∧
      a * (t i) ^ 2 + C < m + 1) :
    s.card ≤ 2 := by
  classical
  have hpos : (s.filter fun i => 0 ≤ t i).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    rcases Finset.mem_filter.mp hi with ⟨his, hit⟩
    rcases Finset.mem_filter.mp hj with ⟨hjs, hjt⟩
    by_contra hij
    exact (not_lt_of_ge (hsep his hjs hij))
      (weighted_nonneg_band_sq_dist_lt_one a C m (t i) (t j)
        ha hit hjt (hband i his) (hband j hjs))
  have hneg : (s.filter fun i => t i < 0).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    rcases Finset.mem_filter.mp hi with ⟨his, hit⟩
    rcases Finset.mem_filter.mp hj with ⟨hjs, hjt⟩
    by_contra hij
    have hd := weighted_nonneg_band_sq_dist_lt_one a C m (-t i) (-t j)
      ha (neg_nonneg.mpr hit.le) (neg_nonneg.mpr hjt.le)
      (by simpa only [neg_sq] using hband i his)
      (by simpa only [neg_sq] using hband j hjs)
    have heq : ((-t i) - (-t j)) ^ 2 = (t i - t j) ^ 2 := by ring
    rw [heq] at hd
    exact (not_lt_of_ge (hsep his hjs hij)) hd
  have hsub : s ⊆ (s.filter fun i => 0 ≤ t i) ∪ (s.filter fun i => t i < 0) := by
    intro i hi
    by_cases ht : 0 ≤ t i
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hi, ht⟩))
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨hi, lt_of_not_ge ht⟩))
  calc
    s.card ≤ ((s.filter fun i => 0 ≤ t i) ∪ (s.filter fun i => t i < 0)).card :=
      Finset.card_le_card hsub
    _ ≤ (s.filter fun i => 0 ≤ t i).card + (s.filter fun i => t i < 0).card :=
      Finset.card_union_le _ _
    _ ≤ 2 := Nat.add_le_add hpos hneg

/-- Unit-separated real parameters in a common scalar squared-norm band. -/
theorem scalar_band_card_le_two {ι : Type uIndex} (s : Finset ι)
    (t : ι → ℝ) (C m : ℝ)
    (hsep : (s : Set ι).Pairwise fun i j => 1 ≤ |t i - t j|)
    (hband : ∀ i ∈ s, m ≤ (t i) ^ 2 + C ∧ (t i) ^ 2 + C < m + 1) :
    s.card ≤ 2 := by
  apply weighted_scalar_band_card_le_two s t 1 C m zero_le_one
  · intro i hi j hj hij
    have hab := hsep hi hj hij
    have hs : (1 : ℝ) ≤ (t i - t j) ^ 2 := by
      nlinarith [sq_nonneg (|t i - t j| - 1), sq_abs (t i - t j)]
    simpa only [one_mul] using hs
  · intro i hi
    simpa only [one_mul] using hband i hi

theorem scalar_band_card_le_four {ι : Type uIndex} (s : Finset ι)
    (t : ι → ℝ) (C m : ℝ)
    (hsep : (s : Set ι).Pairwise fun i j => 1 ≤ |t i - t j|)
    (hband : ∀ i ∈ s, m ≤ (t i) ^ 2 + C ∧ (t i) ^ 2 + C < m + 1) :
    s.card ≤ 4 :=
  (scalar_band_card_le_two s t C m hsep hband).trans (by decide)

/-- Squared distance on an affine line, without Euclidean projection. -/
theorem distSq_affine {D : ℕ} (A B : Vec D) (u v : ℝ) :
    distSq (fun i => A i + u * B i) (fun i => A i + v * B i) =
      normSq B * (u - v) ^ 2 := by
  unfold distSq normSq
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem normSq_affine {D : ℕ} (A B : Vec D) (t : ℝ) :
    normSq (fun i => A i + t * B i) =
      normSq A + 2 * t * (∑ i, A i * B i) + t ^ 2 * normSq B := by
  unfold normSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Completing the scalar quadratic gives the weighted band directly.
The constant term need not be assumed positive for the packing lemma. -/
theorem normSq_affine_complete_square {D : ℕ} (A B : Vec D) (t : ℝ)
    (hB : normSq B ≠ 0) :
    normSq (fun i => A i + t * B i) =
      normSq B * (t + (∑ i, A i * B i) / normSq B) ^ 2 +
        (normSq A - (∑ i, A i * B i) ^ 2 / normSq B) := by
  rw [normSq_affine]
  field_simp [hB]
  ring

end QuantitativeVanDerWaerden

end

end OAI
