import Mathlib

namespace OAI

universe u v w

noncomputable section

namespace Problem313.RestrictionMass

open scoped BigOperators

/-- Parseval for a finite orthonormal family, with an explicit real weight. -/
theorem weighted_sum_sq_expansion
    {B : Type u} {Y : Type v} [Fintype B] [DecidableEq B] [Fintype Y]
    (w : Y → ℝ) (χ : B → Y → ℝ)
    (horth : ∀ b d, (∑ y, w y * χ b y * χ d y) = if b = d then 1 else 0)
    (c : B → ℝ) :
    (∑ y, w y * (∑ b, c b * χ b y) ^ 2) = ∑ b, c b ^ 2 := by
  classical
  calc
    (∑ y, w y * (∑ b, c b * χ b y) ^ 2) =
        ∑ y, ∑ b, ∑ d, c b * c d * (w y * χ b y * χ d y) := by
      apply Finset.sum_congr rfl
      intro y hy
      simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = ∑ b, ∑ d, c b * c d * (∑ y, w y * χ b y * χ d y) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = ∑ b, c b ^ 2 := by
      simp [horth, pow_two]

/-- Averaging the squared restricted coefficients eliminates exterior Fourier
cross terms. No sign or normalization assumption on `w` is needed here. -/
theorem average_restriction_mass
    {A : Type w} {B : Type u} {Y : Type v} [Fintype B] [DecidableEq B] [Fintype Y]
    (w : Y → ℝ) (χ : B → Y → ℝ)
    (horth : ∀ b d, (∑ y, w y * χ b y * χ d y) = if b = d then 1 else 0)
    (c : A → B → ℝ) (L : Finset A) :
    (∑ y, w y * ∑ a ∈ L, (∑ b, c a b * χ b y) ^ 2) =
      ∑ a ∈ L, ∑ b, c a b ^ 2 := by
  classical
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  exact weighted_sum_sq_expansion w χ horth (c a)

/-- The same identity with restricted coefficients supplied as a separate function. -/
theorem average_restriction_mass_of_expansion
    {A : Type w} {B : Type u} {Y : Type v} [Fintype B] [DecidableEq B] [Fintype Y]
    (w : Y → ℝ) (χ : B → Y → ℝ)
    (horth : ∀ b d, (∑ y, w y * χ b y * χ d y) = if b = d then 1 else 0)
    (c : A → B → ℝ) (r : A → Y → ℝ)
    (hr : ∀ a y, r a y = ∑ b, c a b * χ b y) (L : Finset A) :
    (∑ y, w y * ∑ a ∈ L, r a y ^ 2) = ∑ a ∈ L, ∑ b, c a b ^ 2 := by
  simp_rw [hr]
  exact average_restriction_mass w χ horth c L

end Problem313.RestrictionMass

end

end OAI
