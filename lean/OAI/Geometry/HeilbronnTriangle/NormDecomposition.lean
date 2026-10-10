import Mathlib

namespace OAI


namespace Problem355.NormDecomposition

open scoped BigOperators

variable {ι R : Type*} [Fintype ι] [CommRing R]

private theorem sum_swap_first (f : ι → ι → ι → R) :
    (∑ i, ∑ j, ∑ k, f j i k) = ∑ i, ∑ j, ∑ k, f i j k := by
  rw [Finset.sum_comm]

private theorem sum_swap_last (f : ι → ι → ι → R) :
    (∑ i, ∑ j, ∑ k, f i k j) = ∑ i, ∑ j, ∑ k, f i j k := by
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

private theorem sum_rotate (f : ι → ι → ι → R) :
    (∑ i, ∑ j, ∑ k, f k i j) = ∑ i, ∑ j, ∑ k, f i j k := by
  calc
    (∑ i, ∑ j, ∑ k, f k i j) = ∑ i, ∑ j, ∑ k, f j i k :=
      sum_swap_last (fun i j k => f j i k)
    _ = ∑ i, ∑ j, ∑ k, f i j k := sum_swap_first f

private theorem sum_rotate' (f : ι → ι → ι → R) :
    (∑ i, ∑ j, ∑ k, f j k i) = ∑ i, ∑ j, ∑ k, f i j k := by
  calc
    (∑ i, ∑ j, ∑ k, f j k i) = ∑ i, ∑ j, ∑ k, f i k j :=
      sum_swap_first (fun i j k => f i k j)
    _ = ∑ i, ∑ j, ∑ k, f i j k := sum_swap_last f

private theorem sum_reverse (f : ι → ι → ι → R) :
    (∑ i, ∑ j, ∑ k, f k j i) = ∑ i, ∑ j, ∑ k, f i j k := by
  calc
    (∑ i, ∑ j, ∑ k, f k j i) = ∑ i, ∑ j, ∑ k, f j k i :=
      sum_swap_last (fun i j k => f j k i)
    _ = ∑ i, ∑ j, ∑ k, f i j k := sum_rotate' f

variable [LinearOrder ι]

def increasingSum (f : ι → ι → ι → R) : R :=
  ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then f i j k else 0

omit [Fintype ι] in
private theorem partition_pointwise (f : ι → ι → ι → R)
    (h12 : ∀ i k, f i i k = 0) (h13 : ∀ i j, f i j i = 0)
    (h23 : ∀ i j, f i j j = 0) (i j k : ι) :
    f i j k =
      (if i < j ∧ j < k then f i j k else 0) +
      (if i < k ∧ k < j then f i j k else 0) +
      (if j < i ∧ i < k then f i j k else 0) +
      (if j < k ∧ k < i then f i j k else 0) +
      (if k < i ∧ i < j then f i j k else 0) +
      (if k < j ∧ j < i then f i j k else 0) := by
  rcases lt_trichotomy i j with hij | hij | hij
  · rcases lt_trichotomy j k with hjk | hjk | hjk
    · simp only [hij, hjk, lt_trans hij hjk, and_self, ite_true,
        not_lt_of_gt hij, not_lt_of_gt hjk, not_lt_of_gt (lt_trans hij hjk),
        false_and, and_false, ite_false, add_zero]
    · subst k
      simp [h23]
    · rcases lt_trichotomy i k with hik | hik | hik
      · simp [hij, hjk, hik, not_lt_of_gt hij, not_lt_of_gt hjk, not_lt_of_gt hik]
      · subst k
        simp [h13]
      · simp [hij, hjk, hik, not_lt_of_gt hij, not_lt_of_gt hjk, not_lt_of_gt hik]
  · subst j
    simp [h12]
  · rcases lt_trichotomy i k with hik | hik | hik
    · simp [hij, hik, lt_trans hij hik, not_lt_of_gt hij, not_lt_of_gt hik,
        not_lt_of_gt (lt_trans hij hik)]
    · subst k
      simp [h13]
    · rcases lt_trichotomy j k with hjk | hjk | hjk
      · simp [hij, hik, hjk, not_lt_of_gt hij, not_lt_of_gt hik, not_lt_of_gt hjk]
      · subst k
        simp [h23]
      · simp [hij, hik, hjk, not_lt_of_gt hij, not_lt_of_gt hik, not_lt_of_gt hjk]

theorem sum_eq_six_increasing (f : ι → ι → ι → R)
    (h12 : ∀ i k, f i i k = 0) (h13 : ∀ i j, f i j i = 0)
    (h23 : ∀ i j, f i j j = 0) :
    (∑ i, ∑ j, ∑ k, f i j k) =
      increasingSum f + increasingSum (fun i j k => f i k j) +
      increasingSum (fun i j k => f j i k) +
      increasingSum (fun i j k => f k i j) +
      increasingSum (fun i j k => f j k i) +
      increasingSum (fun i j k => f k j i) := by
  have h132 : increasingSum (fun i j k => f i k j) =
      ∑ i, ∑ j, ∑ k, if i < k ∧ k < j then f i j k else 0 :=
    sum_swap_last (fun i j k => if i < k ∧ k < j then f i j k else 0)
  have h213 : increasingSum (fun i j k => f j i k) =
      ∑ i, ∑ j, ∑ k, if j < i ∧ i < k then f i j k else 0 :=
    sum_swap_first (fun i j k => if j < i ∧ i < k then f i j k else 0)
  have h312 : increasingSum (fun i j k => f k i j) =
      ∑ i, ∑ j, ∑ k, if j < k ∧ k < i then f i j k else 0 :=
    sum_rotate (fun i j k => if j < k ∧ k < i then f i j k else 0)
  have h231 : increasingSum (fun i j k => f j k i) =
      ∑ i, ∑ j, ∑ k, if k < i ∧ i < j then f i j k else 0 :=
    sum_rotate' (fun i j k => if k < i ∧ i < j then f i j k else 0)
  have h321 : increasingSum (fun i j k => f k j i) =
      ∑ i, ∑ j, ∑ k, if k < j ∧ j < i then f i j k else 0 :=
    sum_reverse (fun i j k => if k < j ∧ j < i then f i j k else 0)
  rw [h132, h213, h312, h231, h321]
  unfold increasingSum
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  exact partition_pointwise f h12 h13 h23 i j k

theorem alternating_triple_sum (c : ι → ι → ι → R)
    (h12 : ∀ i k, c i i k = 0) (h13 : ∀ i j, c i j i = 0)
    (h23 : ∀ i j, c i j j = 0)
    (hs12 : ∀ i j k, c j i k = -c i j k)
    (hs23 : ∀ i j k, c i k j = -c i j k)
    (x y z : ι → R) :
    (∑ i, ∑ j, ∑ k, c i j k * x i * y j * z k) =
      increasingSum (fun i j k => c i j k *
        Matrix.det !![x i, y i, z i; x j, y j, z j; x k, y k, z k]) := by
  rw [sum_eq_six_increasing
    (fun i j k => c i j k * x i * y j * z k)
    (by intro i k; simp [h12])
    (by intro i j; simp [h13])
    (by intro i j; simp [h23])]
  unfold increasingSum
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : i < j ∧ j < k
  · simp [h, Matrix.det_fin_three]
    have h132 := hs23 i j k
    have h213 := hs12 i j k
    have h312 : c k i j = c i j k := by rw [hs12, h132, neg_neg]
    have h231 : c j k i = c i j k := by rw [hs23, h213, neg_neg]
    have h321 : c k j i = -c i j k := by rw [hs12, h231]
    rw [h132, h213, h312, h231, h321]
    ring
  · simp [h]

theorem alternating_triple_sum_of_two_ne_zero [NoZeroDivisors R]
    (h2 : (2 : R) ≠ 0) (c : ι → ι → ι → R)
    (hs12 : ∀ i j k, c j i k = -c i j k)
    (hs23 : ∀ i j k, c i k j = -c i j k)
    (x y z : ι → R) :
    (∑ i, ∑ j, ∑ k, c i j k * x i * y j * z k) =
      increasingSum (fun i j k => c i j k *
        Matrix.det !![x i, y i, z i; x j, y j, z j; x k, y k, z k]) := by
  have hz (a : R) (ha : a = -a) : a = 0 := by
    have hh : (2 : R) * a = 0 := by linear_combination ha
    exact (mul_eq_zero.mp hh).resolve_left h2
  have h12 : ∀ i k, c i i k = 0 := fun i k => hz _ (hs12 i i k)
  have h23 : ∀ i j, c i j j = 0 := fun i j => hz _ (hs23 i j j)
  have h13 : ∀ i j, c i j i = 0 := by
    intro i j
    rw [hs12, h23, neg_zero]
  exact alternating_triple_sum c h12 h13 h23 hs12 hs23 x y z

end Problem355.NormDecomposition

end OAI
