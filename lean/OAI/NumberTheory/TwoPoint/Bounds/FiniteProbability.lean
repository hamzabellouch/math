import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

namespace OAI

/-!
# Finite weighted sampling for the random-prime rank argument

The prime labels in the rank argument have a nonuniform reciprocal law.
The corresponding finite-sum probability identities account for that law.
-/

namespace TwoPointCorrelations

open Finset

structure FiniteLaw (α : Type*) [Fintype α] where
  weight : α → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1

namespace FiniteLaw

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]

noncomputable def average (μ : FiniteLaw α) (f : α → ℝ) : ℝ :=
  ∑ x, μ.weight x * f x

noncomputable def probability (μ : FiniteLaw α) (E : α → Prop) : ℝ := by
  classical
  exact μ.average (fun x => if E x then 1 else 0)

lemma average_nonneg (μ : FiniteLaw α) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ μ.average f := sum_nonneg (fun x _ => mul_nonneg (μ.nonneg x) (hf x))

lemma average_mono (μ : FiniteLaw α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.average f ≤ μ.average g := sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonneg x))

@[simp] lemma average_const (μ : FiniteLaw α) (c : ℝ) : μ.average (fun _ => c) = c := by
  simp [average, ← sum_mul, μ.total]

lemma average_sum (μ : FiniteLaw α) (f : ι → α → ℝ) :
    μ.average (fun x => ∑ i, f i x) = ∑ i, μ.average (f i) := by
  simp only [average, mul_sum]
  rw [sum_comm]

lemma average_mul_const (μ : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    μ.average (fun x => f x * c) = μ.average f * c := by
  simp only [average, mul_assoc, sum_mul]

lemma average_comm (μ : FiniteLaw α) (ν : FiniteLaw β) (f : α → β → ℝ) :
    μ.average (fun x => ν.average (f x)) = ν.average (fun y => μ.average (fun x => f x y)) := by
  simp only [average, mul_sum]
  rw [sum_comm]
  congr 1
  funext y
  apply sum_congr rfl
  intro x _
  ring

/-- Weighted Cauchy--Schwarz against the constant function one. -/
lemma square_average_le (μ : FiniteLaw α) (f : α → ℝ) :
    (μ.average f) ^ 2 ≤ μ.average (fun x => f x ^ 2) := by
  have h := sum_sq_le_sum_mul_sum_of_sq_le_mul univ
    (f := μ.weight) (g := fun x => μ.weight x * f x ^ 2)
    (r := fun x => μ.weight x * f x)
    (fun x _ => μ.nonneg x)
    (fun x _ => mul_nonneg (μ.nonneg x) (sq_nonneg _))
    (fun x _ => le_of_eq (by ring))
  simpa only [average, μ.total, one_mul] using h

lemma square_average_eq (μ : FiniteLaw α) (f : α → ℝ) :
    (μ.average f) ^ 2 = μ.average (fun x => μ.average (fun y => f x * f y)) := by
  simp only [average, pow_two, mul_sum, sum_mul]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  ring

/-- Repeating the second sample removes every term depending only on the
first sample. This is the Cauchy--Schwarz step of `q:rank-probability`. -/
theorem two_sample_bound (μ : FiniteLaw α) (ν : FiniteLaw β)
    (E : α → β → Prop) (D : α → β → β → Prop)
    (hD : ∀ c y z, E c y → E c z → D c y z) :
    (μ.average (fun c => ν.probability (E c))) ^ 2 ≤
      μ.average (fun c => ν.average (fun y => ν.probability (D c y))) := by
  classical
  apply (μ.square_average_le _).trans
  apply μ.average_mono
  intro c
  rw [probability, ν.square_average_eq]
  apply ν.average_mono
  intro y
  apply ν.average_mono
  intro z
  by_cases hy : E c y <;> by_cases hz : E c z
  · simp [hy, hz, hD c y z hy hz]
  · simp [hy, hz]; split_ifs <;> norm_num
  · simp [hy, hz]; split_ifs <;> norm_num
  · simp [hy, hz]; split_ifs <;> norm_num

noncomputable def product (μ : FiniteLaw α) (ν : FiniteLaw β) : FiniteLaw (α × β) where
  weight x := μ.weight x.1 * ν.weight x.2
  nonneg x := mul_nonneg (μ.nonneg _) (ν.nonneg _)
  total := by simp [Fintype.sum_prod_type, ← mul_sum, μ.total, ν.total]

lemma average_product (μ : FiniteLaw α) (ν : FiniteLaw β) (f : α × β → ℝ) :
    (μ.product ν).average f = μ.average (fun x => ν.average (fun y => f (x, y))) := by
  simp only [average, product, Fintype.sum_prod_type, mul_sum, mul_assoc]

noncomputable def independent [DecidableEq ι] (μ : ι → FiniteLaw α) : FiniteLaw (ι → α) where
  weight x := ∏ i, (μ i).weight (x i)
  nonneg x := prod_nonneg (fun i _ => (μ i).nonneg _)
  total := by
    rw [← Fintype.prod_sum (fun i x => (μ i).weight x)]
    simp only [FiniteLaw.total, prod_const_one]

lemma independent_average_product [DecidableEq ι] (μ : ι → FiniteLaw α) (f : ι → α → ℝ) :
    (independent μ).average (fun x => ∏ i, f i (x i)) = ∏ i, (μ i).average (f i) := by
  simp only [average, independent, ← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => (μ i).weight x * f i x)).symm

lemma probability_nonneg (μ : FiniteLaw α) (E : α → Prop) : 0 ≤ μ.probability E := by
  classical
  apply μ.average_nonneg
  intro x
  split_ifs <;> norm_num

lemma probability_le_one (μ : FiniteLaw α) (E : α → Prop) : μ.probability E ≤ 1 := by
  classical
  apply (μ.average_mono (g := fun _ => 1) ?_).trans_eq (μ.average_const 1)
  intro x
  split_ifs <;> norm_num

/-- If an event contains at most one atom, its mass is bounded by the
largest allowed atom. This is used after fixing the nonpivot labels. -/
lemma probability_le_atom_bound (μ : FiniteLaw α) (E : α → Prop) (a : ℝ)
    (ha : 0 ≤ a) (hatom : ∀ x, μ.weight x ≤ a)
    (hunique : ∀ x y, E x → E y → x = y) : μ.probability E ≤ a := by
  classical
  by_cases he : ∃ x, E x
  · obtain ⟨x, hx⟩ := he
    have hE (y : α) : E y ↔ y = x := ⟨fun hy => hunique y x hy hx, fun hy => hy ▸ hx⟩
    simpa [probability, average, hE] using hatom x
  · have hE (x : α) : ¬ E x := fun hx => he ⟨x, hx⟩
    simpa [probability, average, hE] using ha

end FiniteLaw

end TwoPointCorrelations

end OAI
