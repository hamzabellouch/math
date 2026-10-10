import OAI.Geometry.Zonotope.Decomposition
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

noncomputable section
open Set
open scoped BigOperators

namespace DiagonalZonotope
variable {ι : Type*} [Fintype ι]

/-- The translate of the diagonal zonotope centered at the origin. -/
def centered : Set (ι → ℝ) := {x | (fun j => x j + 1) ∈ zonotope}

/-- Coordinate and coordinate-difference inequalities describe the centered body exactly. -/
theorem mem_centered_iff (x : ι → ℝ) :
    x ∈ centered ↔ (∀ i, |x i| ≤ 1) ∧ ∀ i j, |x i - x j| ≤ 1 := by
  classical
  constructor
  · rintro ⟨q, hq, t, ht, hx⟩
    have heq (j : ι) : x j + 1 = q j + t := by simpa using congrFun hx j
    constructor
    · intro i
      apply abs_le.mpr
      constructor <;> linarith [heq i, (hq i).1, (hq i).2, ht.1, ht.2]
    · intro i j
      apply abs_le.mpr
      constructor <;> linarith [heq i, heq j, (hq i).1, (hq i).2, (hq j).1, (hq j).2]
  · rintro ⟨hab, hdiff⟩
    by_cases hn : ∀ j, x j ≤ 0
    · refine ⟨fun j => x j + 1, ?_, 0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      · intro j
        constructor <;> linarith [(abs_le.mp (hab j)).1, hn j]
      · funext j
        simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, zero_mul, add_zero]
    · have hp : ∃ k, 0 < x k := by simpa only [not_forall, not_le] using hn
      obtain ⟨k, hk⟩ := hp
      obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ x
        ⟨k, Finset.mem_univ k⟩
      have hm (j : ι) : x j ≤ x i := hmax j (Finset.mem_univ j)
      refine ⟨fun j => x j + 1 - x i, ?_, x i, ?_, ?_⟩
      · intro j
        constructor
        · linarith [(abs_le.mp (hdiff j i)).1]
        · linarith [hm j]
      · exact ⟨le_of_lt (lt_of_lt_of_le hk (hm k)), (abs_le.mp (hab i)).2⟩
      · funext j
        simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
        exact (sub_add_cancel _ _).symm

lemma interval_mul_bound (a r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    2 * (a * r) ≤ |a| + a := by
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
    linarith [mul_le_mul_of_nonneg_left hr1 ha]
  · rw [abs_of_neg (lt_of_not_ge ha)]
    linarith [mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge ha)) hr0]

lemma interval_mul_max (a : ℝ) :
    2 * (a * (if 0 ≤ a then 1 else 0)) = |a| + a := by
  by_cases ha : 0 ≤ a
  · simp [ha, abs_of_nonneg ha, two_mul]
  · simp [ha, abs_of_neg (lt_of_not_ge ha)]

/-- Every point satisfies the exact support bound, expressed as a coordinate pairing. -/
theorem centered_support_le (u x : ι → ℝ) (hx : x ∈ centered) :
    (∑ i, u i * x i) ≤ ((∑ i, |u i|) + |∑ i, u i|) / 2 := by
  rcases hx with ⟨q, hq, t, ht, hx⟩
  have heq (i : ι) : x i = q i + t - 1 := by
    have h : x i + 1 = q i + t := by simpa using congrFun hx i
    linarith
  have hqbound := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    interval_mul_bound (u i) (q i) (hq i).1 (hq i).2)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hqbound
  have htbound := interval_mul_bound (∑ i, u i) t ht.1 ht.2
  have hdot : (∑ i, u i * x i) =
      (∑ i, u i * q i) + (∑ i, u i) * t - ∑ i, u i := by
    simp only [heq, mul_sub, mul_add, mul_one, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_mul]
  linarith

/-- A sign-selected point attains the support bound in every direction. -/
theorem centered_support_attained (u : ι → ℝ) :
    ∃ x ∈ centered, (∑ i, u i * x i) =
      ((∑ i, |u i|) + |∑ i, u i|) / 2 := by
  classical
  let q : ι → ℝ := fun i => if 0 ≤ u i then 1 else 0
  let t : ℝ := if 0 ≤ ∑ i, u i then 1 else 0
  let x : ι → ℝ := fun i => q i + t - 1
  have hq : q ∈ cube := by
    intro i
    dsimp [q]
    split_ifs <;> constructor <;> norm_num
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    dsimp [t]
    split_ifs <;> constructor <;> norm_num
  refine ⟨x, ?_, ?_⟩
  · refine ⟨q, hq, t, ht, ?_⟩
    funext i
    simp only [x, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact sub_add_cancel _ _
  · have hqeq := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
      interval_mul_max (u i))
    change (∑ i, 2 * (u i * q i)) = ∑ i, (|u i| + u i) at hqeq
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hqeq
    have hteq := interval_mul_max (∑ i, u i)
    change 2 * ((∑ i, u i) * t) = |∑ i, u i| + ∑ i, u i at hteq
    have hdot : (∑ i, u i * x i) =
        (∑ i, u i * q i) + (∑ i, u i) * t - ∑ i, u i := by
      simp only [x, mul_sub, mul_add, mul_one, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, Finset.sum_mul]
    linarith

end DiagonalZonotope

end

end OAI
