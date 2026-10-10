import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CrossCovariance

variable {α β : Type*} [sectionFintypeα : Fintype α] [Fintype β]

def jointMoment (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (f : α → ℝ) (g : β → ℝ) : ℝ :=
  ∑ x, ∑ y, a x * b y * (2 - p x - q y) * f x * g y

def mass (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ) : ℝ :=
  jointMoment a b p q (fun _ => 1) (fun _ => 1)

def jointAverage (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (f : α → ℝ) (g : β → ℝ) : ℝ :=
  jointMoment a b p q f g / mass a b p q

theorem jointMoment_eq (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (f : α → ℝ) (g : β → ℝ) :
    jointMoment a b p q f g =
      2 * (∑ x, a x * f x) * (∑ y, b y * g y) -
      (∑ x, a x * p x * f x) * (∑ y, b y * g y) -
      (∑ x, a x * f x) * (∑ y, b y * q y * g y) := by
  unfold jointMoment
  calc
    (∑ x, ∑ y, a x * b y * (2 - p x - q y) * f x * g y) =
        ∑ x, ∑ y, (2 * (a x * f x) * (b y * g y) -
          (a x * p x * f x) * (b y * g y) -
          (a x * f x) * (b y * q y * g y)) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]

theorem mass_eq (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ) :
    mass a b p q = 2 * (∑ x, a x) * (∑ y, b y) -
      (∑ x, a x * p x) * (∑ y, b y) -
      (∑ x, a x) * (∑ y, b y * q y) := by
  simp [mass, jointMoment_eq]

theorem covariance_rank_one
    (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (f : α → ℝ) (g : β → ℝ) :
    jointAverage a b p q f g -
        jointAverage a b p q f (fun _ => 1) *
          jointAverage a b p q (fun _ => 1) g =
      - ((∑ x, a x) * (∑ x, a x * p x * f x) -
          (∑ x, a x * p x) * (∑ x, a x * f x)) *
        ((∑ y, b y) * (∑ y, b y * q y * g y) -
          (∑ y, b y * q y) * (∑ y, b y * g y)) /
        (mass a b p q) ^ 2 := by
  by_cases hZ : mass a b p q = 0
  · simp [jointAverage, hZ]
  · unfold jointAverage
    rw [jointMoment_eq, jointMoment_eq, jointMoment_eq]
    simp only [mul_one]
    field_simp
    rw [mass_eq]
    ring

def rightSliceAverage (b : β → ℝ) (q : β → ℝ) (t : ℝ) (g : β → ℝ) : ℝ :=
  (∑ y, b y * (2 - t - q y) * g y) / (∑ y, b y * (2 - t - q y))

theorem rightSliceAverage_eq (b : β → ℝ) (q : β → ℝ) (t : ℝ) (g : β → ℝ) :
    rightSliceAverage b q t g =
      ((2 - t) * (∑ y, b y * g y) - (∑ y, b y * q y * g y)) /
        ((2 - t) * (∑ y, b y) - (∑ y, b y * q y)) := by
  unfold rightSliceAverage
  congr 1
  · calc
      (∑ y, b y * (2 - t - q y) * g y) =
          ∑ y, ((2 - t) * (b y * g y) - b y * q y * g y) := by
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  · calc
      (∑ y, b y * (2 - t - q y)) =
          ∑ y, ((2 - t) * b y - b y * q y) := by
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

include sectionFintypeα in
theorem rightSliceAverage_span (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (hp : ∀ x, p x = 0 ∨ p x = 1) (g : β → ℝ) (x : α) :
    rightSliceAverage b q (p x) g =
      rightSliceAverage b q 0 g +
        (rightSliceAverage b q 1 g - rightSliceAverage b q 0 g) * p x := by
  have retainedsectionFintypeα := sectionFintypeα
  rcases hp x with h | h <;> rw [h] <;> ring

theorem offCenter_jointMoment_zero
    (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (hp : ∀ x, p x = 0 ∨ p x = 1) (hq : ∀ y, q y = 0 ∨ q y = 1) :
    jointMoment a b p q p q = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  rcases hp x with hpx | hpx <;> rcases hq y with hqy | hqy <;>
    norm_num [hpx, hqy]

theorem offCenter_covariance
    (a : α → ℝ) (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (hp : ∀ x, p x = 0 ∨ p x = 1) (hq : ∀ y, q y = 0 ∨ q y = 1) :
    jointAverage a b p q p q -
        jointAverage a b p q p (fun _ => 1) *
          jointAverage a b p q (fun _ => 1) q =
      -(jointAverage a b p q p (fun _ => 1) *
          jointAverage a b p q (fun _ => 1) q) := by
  have h : jointAverage a b p q p q = 0 := by
    simp only [jointAverage, offCenter_jointMoment_zero a b p q hp hq, zero_div]
  rw [h]
  ring

end Problem315.CrossCovariance

end

end OAI
