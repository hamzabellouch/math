import Mathlib

namespace OAI

noncomputable section

namespace Problem355

abbrev Point := ℝ × ℝ

def triangleArea (p q r : Point) : ℝ :=
  abs ((q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)) / 2

def pointInUnitSquare (p : Point) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1

def pointsInUnitSquare (P : Finset Point) : Prop := by
  classical
  exact ∀ p, p ∈ P → pointInUnitSquare p

def triangleAreasAtLeast (P : Finset Point) (a : ℝ) : Prop := by
  classical
  exact ∀ p, p ∈ P → ∀ q, q ∈ P → ∀ r, r ∈ P →
    p ≠ q → p ≠ r → q ≠ r → a ≤ triangleArea p q r

def hasTriangleAreaAtMost (P : Finset Point) (a : ℝ) : Prop := by
  classical
  exact ∃ p, p ∈ P ∧ ∃ q, q ∈ P ∧ ∃ r, r ∈ P ∧
    p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ triangleArea p q r ≤ a

def heilbronnD : ℕ := 41

def heilbronnM : ℕ := Nat.choose (4 * heilbronnD - 1) heilbronnD

def heilbronnT : ℕ := Nat.choose heilbronnM 3

def heilbronnK : ℕ := heilbronnT ^ 2 + 1

def heilbronnExponent : ℝ :=
  1 / (100000 * (heilbronnK : ℝ))

def eventualAlmostUpperBound (epsilon : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → 3 ≤ n →
    ∀ P : Finset Point, P.card = n → pointsInUnitSquare P →
      hasTriangleAreaAtMost P
        (C * Real.rpow (n : ℝ) (-2 + epsilon))

attribute [local irreducible] Problem355.heilbronnT
  Problem355.heilbronnM

theorem heilbronn_power_lower_bound :
    0 < heilbronnExponent ∧ ∃ n : ℕ → ℕ, ∃ P : ℕ → Finset Point,
      Filter.Tendsto n Filter.atTop Filter.atTop ∧ ∀ j : ℕ,
        3 ≤ n j ∧ (P j).card = n j ∧ pointsInUnitSquare (P j) ∧
        triangleAreasAtLeast (P j)
          (Real.rpow (n j : ℝ) (-2 + heilbronnExponent)) := by
  sorry

theorem almost_n_minus_two_refuted :
    0 < heilbronnExponent / 2 ∧
      ¬ eventualAlmostUpperBound (heilbronnExponent / 2) := by
  sorry

end Problem355

end

end OAI
