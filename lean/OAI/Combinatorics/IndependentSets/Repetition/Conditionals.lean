import Mathlib
import OAI.Combinatorics.IndependentSets.Repetition.Finite

namespace OAI

namespace IndependentSetsGames.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def conditionalKernel
    (p : α × β → ℝ) (fallback : β → ℝ) (a : α) (b : β) : ℝ := by
  classical
  exact if firstMarginal p a = 0 then fallback b
    else p (a, b) / firstMarginal p a

theorem conditionalKernel_isProbability
    (p : α × β → ℝ) (fallback : β → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) (a : α) :
    IsProbability (conditionalKernel p fallback a) := by
  classical
  by_cases hm : firstMarginal p a = 0
  · simpa only [IsProbability, conditionalKernel, ite_eq_left hm] using hf
  · constructor
    · intro b
      simp only [conditionalKernel, ite_eq_right hm]
      exact div_nonneg (hp.1 (a, b))
        ((firstMarginal_isProbability p hp).1 a)
    · simp only [conditionalKernel, ite_eq_right hm, div_eq_mul_inv, ← Finset.sum_mul]
      change firstMarginal p a * (firstMarginal p a)⁻¹ = 1
      exact mul_inv_cancel₀ hm

theorem marginal_mul_conditionalKernel
    (p : α × β → ℝ) (fallback : β → ℝ)
    (hp : IsProbability p) (a : α) (b : β) :
    firstMarginal p a * conditionalKernel p fallback a b = p (a, b) := by
  classical
  by_cases hm : firstMarginal p a = 0
  · have hpoint := point_le_firstMarginal p hp a b
    rw [hm] at hpoint
    have hz : p (a, b) = 0 := le_antisymm hpoint (hp.1 (a, b))
    simp [conditionalKernel, hm, hz]
  · simp only [conditionalKernel, ite_eq_right hm]
    calc
      firstMarginal p a * (p (a, b) / firstMarginal p a)
          = p (a, b) *
              (firstMarginal p a / firstMarginal p a) := by ring
      _ = p (a, b) := by rw [div_self hm, mul_one]

theorem law_of_total_probability
    (p : α × β → ℝ) (fallback : β → ℝ)
    (hp : IsProbability p) (b : β) :
    (∑ a, firstMarginal p a * conditionalKernel p fallback a b) =
      secondMarginal p b := by
  simp only [marginal_mul_conditionalKernel p fallback hp, secondMarginal]

theorem kernelProduct_isProbability
    (r : α → ℝ) (k : α → β → ℝ)
    (hr : IsProbability r) (hk : ∀ a, IsProbability (k a)) :
    IsProbability (fun ab : α × β => r ab.1 * k ab.1 ab.2) := by
  constructor
  · intro ab
    exact mul_nonneg (hr.1 ab.1) ((hk ab.1).1 ab.2)
  · simp only [Fintype.sum_prod_type, ← Finset.mul_sum,
      (hk _).2, mul_one, hr.2]

theorem alternativeInput_conditionalProduct_isProbability
    (p : α × β → ℝ) (fallback : β → ℝ) (r : α → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback)
    (hr : IsProbability r) :
    IsProbability
      (fun ab : α × β => r ab.1 * conditionalKernel p fallback ab.1 ab.2) :=
  kernelProduct_isProbability r (conditionalKernel p fallback) hr
    (conditionalKernel_isProbability p fallback hp hf)

theorem totalVariation_joint_common_weights (w : α → ℝ) (p q : α → β → ℝ)
    (hw : ∀ a, 0 ≤ w a) :
    totalVariation (fun ab : α × β => w ab.1 * p ab.1 ab.2)
      (fun ab : α × β => w ab.1 * q ab.1 ab.2) =
        ∑ a, w a * totalVariation (p a) (q a) := by
  have hpoint : ∀ a b, |w a * p a b - w a * q a b| = w a * |p a b - q a b| := by
    intro a b
    rw [← mul_sub, abs_mul, abs_of_nonneg (hw a)]
  simp only [totalVariation, Fintype.sum_prod_type, hpoint, ← Finset.mul_sum,
    div_eq_mul_inv, Finset.sum_mul, mul_assoc]

theorem totalVariation_joint_common_kernel (p q : α → ℝ) (k : α → β → ℝ)
    (hk : ∀ a, IsProbability (k a)) :
    totalVariation (fun ab : α × β => p ab.1 * k ab.1 ab.2)
      (fun ab : α × β => q ab.1 * k ab.1 ab.2) = totalVariation p q := by
  have hpoint : ∀ a b, |p a * k a b - q a * k a b| = |p a - q a| * k a b := by
    intro a b
    rw [← sub_mul, abs_mul, abs_of_nonneg ((hk a).1 b)]
  simp only [totalVariation, Fintype.sum_prod_type, hpoint, ← Finset.mul_sum,
    (hk _).2, mul_one]

theorem totalVariation_condition_le (p q : α → ℝ) (event : α → Prop)
    [DecidablePred event] {c : ℝ} (hc : 0 < c) :
    totalVariation (fun a => if event a then p a / c else 0)
      (fun a => if event a then q a / c else 0) ≤ totalVariation p q / c := by
  have hpoint : ∀ a, |(if event a then p a / c else 0) -
      (if event a then q a / c else 0)| ≤ |p a - q a| / c := by
    intro a
    by_cases he : event a
    · simp only [ite_eq_left he, ← sub_div, abs_div, abs_of_pos hc, le_refl]
    · simp only [ite_eq_right he, sub_self, abs_zero]
      exact div_nonneg (abs_nonneg _) hc.le
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simp only [div_eq_mul_inv, ← Finset.sum_mul] at hsum
  have hd := div_le_div_of_nonneg_right hsum (show (0 : ℝ) ≤ 2 by norm_num)
  have hreorder : ((∑ a, |p a - q a|) * c⁻¹) / 2 =
      ((∑ a, |p a - q a|) / 2) / c := by ring
  rw [hreorder] at hd
  simpa only [totalVariation, div_eq_mul_inv] using hd

theorem weighted_coordinate_sum_sq_le
    (w : α → ℝ) (d : α → β → ℝ) (C : α → ℝ)
    (hw : IsProbability w)
    (hbudget : ∀ a, w a * (∑ b, d a b ^ 2) ≤ w a * C a) :
    (∑ b, ∑ a, w a * d a b)^2 ≤
      (Fintype.card β : ℝ) * (∑ a, w a * C a) := by
  have hv := Finset.sum_le_sum
    (fun b (_ : b ∈ (Finset.univ : Finset β)) =>
      weighted_sum_sq_le w (fun a => d a b) hw)
  have he :
      (∑ b, ∑ a, w a * d a b ^ 2) =
        ∑ a, w a * (∑ b, d a b ^ 2) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [he] at hv
  have hb := Finset.sum_le_sum
    (fun a (_ : a ∈ (Finset.univ : Finset α)) => hbudget a)
  have hs := hv.trans hb
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset β)
    (fun b => ∑ a, w a * d a b) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
  calc
    (∑ b, ∑ a, w a * d a b)^2
        ≤ (∑ b, (∑ a, w a * d a b)^2) *
            (Fintype.card β : ℝ) := hcs
    _ = (Fintype.card β : ℝ) *
          (∑ b, (∑ a, w a * d a b)^2) := mul_comm _ _
    _ ≤ (Fintype.card β : ℝ) * (∑ a, w a * C a) :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)

end IndependentSetsGames.Foundations.Information

end OAI
