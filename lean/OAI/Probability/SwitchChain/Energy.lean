import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FiniteEnergy

variable {α : Type*} [Fintype α]

theorem column_sum_of_symmetric
    (P : α → α → ℝ)
    (hsymm : ∀ i j, P i j = P j i)
    (hrow : ∀ i, ∑ j, P i j = 1) :
    ∀ j, ∑ i, P i j = 1 := by
  intro j
  simpa only [hsymm] using hrow j

theorem sum_sq_sub
    (P : α → α → ℝ)
    (hrow : ∀ i, ∑ j, P i j = 1)
    (hcol : ∀ j, ∑ i, P i j = 1)
    (f : α → ℝ) :
    (∑ i, ∑ j, P i j * (f i - f j) ^ 2) =
      2 * ((∑ i, (f i) ^ 2) - ∑ i, ∑ j, P i j * f i * f j) := by
  have hfirst : (∑ i, ∑ j, P i j * (f i) ^ 2) = ∑ i, (f i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_mul, hrow i, one_mul]
  have hsecond : (∑ i, ∑ j, P i j * (f j) ^ 2) = ∑ j, (f j) ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.sum_mul, hcol j, one_mul]
  calc
    (∑ i, ∑ j, P i j * (f i - f j) ^ 2) =
        ∑ i, ∑ j, (P i j * (f i) ^ 2 + P i j * (f j) ^ 2 -
          2 * (P i j * f i * f j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ i, ∑ j, P i j * (f i) ^ 2) +
        (∑ i, ∑ j, P i j * (f j) ^ 2) -
        2 * (∑ i, ∑ j, P i j * f i * f j) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [hfirst, hsecond]; ring

theorem dirichlet_eq_half_sum
    (P : α → α → ℝ)
    (hrow : ∀ i, ∑ j, P i j = 1)
    (hcol : ∀ j, ∑ i, P i j = 1)
    (f : α → ℝ) :
    (∑ i, f i * (f i - ∑ j, P i j * f j)) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, P i j * (f i - f j) ^ 2 := by
  rw [sum_sq_sub P hrow hcol f]
  have hterm (i : α) : f i * (f i - ∑ j, P i j * f j) =
      (f i) ^ 2 - ∑ j, P i j * f i * f j := by
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j hj
      ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  ring

theorem uniform_dirichlet_eq
    (P : α → α → ℝ)
    (hrow : ∀ i, ∑ j, P i j = 1)
    (hcol : ∀ j, ∑ i, P i j = 1)
    (f : α → ℝ) :
    (∑ i, f i * (f i - ∑ j, P i j * f j)) / (Fintype.card α : ℝ) =
      (∑ i, ∑ j, P i j * (f i - f j) ^ 2) / (2 * (Fintype.card α : ℝ)) := by
  rw [dirichlet_eq_half_sum P hrow hcol f]
  ring

theorem dirichlet_nonneg
    (P : α → α → ℝ)
    (hrow : ∀ i, ∑ j, P i j = 1)
    (hcol : ∀ j, ∑ i, P i j = 1)
    (hP : ∀ i j, 0 ≤ P i j)
    (f : α → ℝ) :
    0 ≤ ∑ i, f i * (f i - ∑ j, P i j * f j) := by
  rw [dirichlet_eq_half_sum P hrow hcol f]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (hP i j) (sq_nonneg _)

theorem dirichlet_add_const
    (P : α → α → ℝ)
    (hrow : ∀ i, ∑ j, P i j = 1)
    (hcol : ∀ j, ∑ i, P i j = 1)
    (f : α → ℝ) (c : ℝ) :
    (∑ i, (f i + c) * ((f i + c) - ∑ j, P i j * (f j + c))) =
      ∑ i, f i * (f i - ∑ j, P i j * f j) := by
  rw [dirichlet_eq_half_sum P hrow hcol (fun i => f i + c),
    dirichlet_eq_half_sum P hrow hcol f]
  simp only [add_sub_add_right_eq_sub]

theorem dirichlet_eq_zero_iff
    (P : α → α → ℝ)
    (hrow : ∀ i, ∑ j, P i j = 1)
    (hcol : ∀ j, ∑ i, P i j = 1)
    (hP : ∀ i j, 0 ≤ P i j)
    (f : α → ℝ) :
    (∑ i, f i * (f i - ∑ j, P i j * f j)) = 0 ↔
      ∀ i j, 0 < P i j → f i = f j := by
  rw [dirichlet_eq_half_sum P hrow hcol f]
  have hn (i j : α) : 0 ≤ P i j * (f i - f j) ^ 2 :=
    mul_nonneg (hP i j) (sq_nonneg _)
  constructor
  · intro h i j hp
    have hs : (∑ i, ∑ j, P i j * (f i - f j) ^ 2) = 0 := by
      linarith
    have hi : (∑ j, P i j * (f i - f j) ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg (fun j _ => hn i j))).mp hs i (Finset.mem_univ i)
    have hij : P i j * (f i - f j) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn i j)).mp hi j (Finset.mem_univ j)
    have hsq : (f i - f j) ^ 2 = 0 :=
      (mul_eq_zero.mp hij).resolve_left (ne_of_gt hp)
    nlinarith [sq_nonneg (f i - f j)]
  · intro h
    have hs : (∑ i, ∑ j, P i j * (f i - f j) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hp : 0 < P i j
      · simp [h i j hp]
      · have hz : P i j = 0 := le_antisymm (le_of_not_gt hp) (hP i j)
        simp [hz]
    rw [hs, mul_zero]

theorem row_square_le
    (P : α → α → ℝ)
    (hrow : ∀ i, ∑ j, P i j = 1)
    (hP : ∀ i j, 0 ≤ P i j)
    (f : α → ℝ) (i : α) :
    (∑ j, P i j * f j) ^ 2 ≤ ∑ j, P i j * (f j) ^ 2 := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun j => P i j * f j) (f := fun j => P i j)
    (g := fun j => P i j * (f j) ^ 2)
    (fun j _ => hP i j)
    (fun j _ => mul_nonneg (hP i j) (sq_nonneg _))
    (fun j _ => by ring_nf; exact le_rfl)
  simpa only [hrow i, one_mul] using h

theorem l2_contraction
    (P : α → α → ℝ)
    (hrow : ∀ i, ∑ j, P i j = 1)
    (hcol : ∀ j, ∑ i, P i j = 1)
    (hP : ∀ i j, 0 ≤ P i j)
    (f : α → ℝ) :
    (∑ i, (∑ j, P i j * f j) ^ 2) ≤ ∑ i, (f i) ^ 2 := by
  calc
    (∑ i, (∑ j, P i j * f j) ^ 2) ≤ ∑ i, ∑ j, P i j * (f j) ^ 2 :=
      Finset.sum_le_sum (fun i _ => row_square_le P hrow hP f i)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_mul, hcol j, one_mul]

theorem sum_apply
    (P : α → α → ℝ)
    (hcol : ∀ j, ∑ i, P i j = 1)
    (f : α → ℝ) :
    (∑ i, ∑ j, P i j * f j) = ∑ j, f j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_mul, hcol j, one_mul]

theorem quadratic_lower_bound
    (P : α → α → ℝ)
    (hrow : ∀ i, ∑ j, P i j = 1)
    (hcol : ∀ j, ∑ i, P i j = 1)
    (hP : ∀ i j, 0 ≤ P i j)
    (f : α → ℝ) :
    -(∑ i, (f i) ^ 2) ≤ ∑ i, f i * (∑ j, P i j * f j) := by
  have hc := l2_contraction P hrow hcol hP f
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f
    (fun i => ∑ j, P i j * f j)
  have hn : 0 ≤ ∑ i, (f i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_left hc hn
  nlinarith

end Problem315.FiniteEnergy

end

end OAI
