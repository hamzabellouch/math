import OAI.Probability.SwitchChain.CrossCellMoments
import OAI.Probability.SwitchChain.CrossIndependent

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CrossCellMoments

variable {α β : Type*} [Fintype α] [Fintype β]

theorem average_product_eq_countAverage (s : ℕ)
    (r : α → Fin 3) (c : β → Fin 3) (f : α → ℝ) (g : β → ℝ) :
    average s r c (fun x y => f x * g y) =
      CrossBlock.countAverage s (fun _ => 1) (fun _ => 1) r c f g := by
  have hsum : (∑ z : Cell s r c, f z.val.2.1 * g z.val.2.2) =
      CrossBlock.countMoment s (fun _ => 1) (fun _ => 1) r c f g := by
    simpa only [CrossBlock.countMoment, one_mul, mul_assoc] using
      sum_cell s r c (fun x y => f x * g y)
  have hcard : (Fintype.card (Cell s r c) : ℝ) =
      CrossBlock.countMoment s (fun _ => 1) (fun _ => 1) r c
        (fun _ => 1) (fun _ => 1) := by
    simpa only [CrossBlock.countMoment, one_mul, mul_one, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul] using sum_cell s r c (fun _ _ => (1 : ℝ))
  exact congrArg₂ (fun x y : ℝ => x / y) hsum hcard

theorem average_product_independent_of_ne_two (s : ℕ) (hs : s ≠ 2)
    (r : α → Fin 3) (c : β → Fin 3) (f : α → ℝ) (g : β → ℝ) :
    average s r c (fun x y => f x * g y) =
      average s r c (fun x _ => f x) * average s r c (fun _ y => g y) := by
  have h := CrossBlock.countAverage_independent s hs
    (fun _ : α => 1) (fun _ : β => 1) r c f g
  rw [← average_product_eq_countAverage s r c f g,
    ← average_product_eq_countAverage s r c f (fun _ => 1),
    ← average_product_eq_countAverage s r c (fun _ => 1) g] at h
  simpa only [mul_one, one_mul] using h

theorem average_product_independent_of_left_event_zero
    (r : α → Fin 3) (c : β → Fin 3)
    (hzero : average 2 r c (fun x _ => offCenter r x) = 0)
    (f : α → ℝ) (g : β → ℝ) :
    average 2 r c (fun x y => f x * g y) =
      average 2 r c (fun x _ => f x) * average 2 r c (fun _ y => g y) := by
  have hp : CrossCovariance.jointAverage (fun _ : α => 1) (fun _ : β => 1)
      (offCenter r) (offCenter c) (offCenter r) (fun _ => 1) = 0 := by
    rw [← average_product_eq]
    simpa only [mul_one] using hzero
  have h := CrossCovariance.independent_of_left_event_zero
    (fun _ : α => 1) (fun _ : β => 1) (offCenter r) (offCenter c)
    (fun _ => zero_le_one) (fun _ => zero_le_one)
    (offCenter_boolean r) (offCenter_boolean c) hp f g
  rw [← average_product_eq r c f g,
    ← average_product_eq r c f (fun _ => 1),
    ← average_product_eq r c (fun _ => 1) g] at h
  simpa only [mul_one, one_mul] using h

theorem average_product_independent_of_right_event_zero
    (r : α → Fin 3) (c : β → Fin 3)
    (hzero : average 2 r c (fun _ y => offCenter c y) = 0)
    (f : α → ℝ) (g : β → ℝ) :
    average 2 r c (fun x y => f x * g y) =
      average 2 r c (fun x _ => f x) * average 2 r c (fun _ y => g y) := by
  have hp : CrossCovariance.jointAverage (fun _ : α => 1) (fun _ : β => 1)
      (offCenter r) (offCenter c) (fun _ => 1) (offCenter c) = 0 := by
    rw [← average_product_eq]
    simpa only [one_mul] using hzero
  have h := CrossCovariance.independent_of_right_event_zero
    (fun _ : α => 1) (fun _ : β => 1) (offCenter r) (offCenter c)
    (fun _ => zero_le_one) (fun _ => zero_le_one)
    (offCenter_boolean r) (offCenter_boolean c) hp f g
  rw [← average_product_eq r c f g,
    ← average_product_eq r c f (fun _ => 1),
    ← average_product_eq r c (fun _ => 1) g] at h
  simpa only [mul_one, one_mul] using h

theorem average_product_independent_of_center_zero
    (r : α → Fin 3) (c : β → Fin 3)
    (hzero : average 2 r c (fun x y => (1 - offCenter r x) * (1 - offCenter c y)) = 0)
    (f : α → ℝ) (g : β → ℝ) :
    average 2 r c (fun x y => f x * g y) =
      average 2 r c (fun x _ => f x) * average 2 r c (fun _ y => g y) := by
  rw [average_product_eq] at hzero
  have h := CrossCovariance.independent_of_center_zero
    (fun _ : α => 1) (fun _ : β => 1) (offCenter r) (offCenter c)
    (fun _ => zero_le_one) (fun _ => zero_le_one)
    (offCenter_boolean r) (offCenter_boolean c) hzero f g
  rw [← average_product_eq r c f g,
    ← average_product_eq r c f (fun _ => 1),
    ← average_product_eq r c (fun _ => 1) g] at h
  simpa only [mul_one, one_mul] using h

theorem average_product_independent_of_degenerate
    (r : α → Fin 3) (c : β → Fin 3)
    (hdeg : average 2 r c (fun x _ => offCenter r x) = 0 ∨
      average 2 r c (fun _ y => offCenter c y) = 0 ∨
      average 2 r c (fun x y => (1 - offCenter r x) * (1 - offCenter c y)) = 0)
    (f : α → ℝ) (g : β → ℝ) :
    average 2 r c (fun x y => f x * g y) =
      average 2 r c (fun x _ => f x) * average 2 r c (fun _ y => g y) := by
  rcases hdeg with h | h | h
  · exact average_product_independent_of_left_event_zero r c h f g
  · exact average_product_independent_of_right_event_zero r c h f g
  · exact average_product_independent_of_center_zero r c h f g

end Problem315.CrossCellMoments

end

end OAI
