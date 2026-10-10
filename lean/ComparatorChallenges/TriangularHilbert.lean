import Mathlib

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace TriangularHilbert

abbrev Plane := ℝ × ℝ

structure Endpoints where
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_lt_upper : lower < upper

def annulus (ε R : ℝ) : Set ℝ := {t | ε < |t| ∧ |t| < R}

def integrand (F G : Plane → ℂ) (z : Plane) (t : ℝ) : ℂ :=
  F (z.1 + t, z.2) * G (z.1, z.2 + t) / (t : ℂ)

def truncation (F G : Plane → ℂ) (E : Endpoints) (z : Plane) : ℂ :=
  ∫ t in annulus E.lower E.upper, integrand F G z t

def GoodPoint (F G : Plane → ℂ) (z : Plane) : Prop :=
  ∀ n : ℕ, IntegrableOn (integrand F G z)
    (annulus (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2))

def maximal (F G : Plane → ℂ) (z : Plane) : ℝ≥0∞ := by
  classical
  exact if GoodPoint F G z then
    ⨆ E : Endpoints, ENNReal.ofReal ‖truncation F G E z‖ else 0

def maximalNorm (F G : Plane → ℂ) : ℝ≥0∞ :=
  (∫⁻ z : Plane, maximal F G z ^ ((3 : ℝ) / 2)) ^ ((2 : ℝ) / 3)

def MainEstimate : Prop :=
  ∃ C : ℝ≥0, ∀ F G : Plane → ℂ,
    MemLp F 3 volume → MemLp G 3 volume →
    (∀ᵐ z ∂volume, GoodPoint F G z) ∧
    AEMeasurable (maximal F G) volume ∧
    maximalNorm F G ≤ (C : ℝ≥0∞) * eLpNorm F 3 volume * eLpNorm G 3 volume

open MeasureTheory Filter
open scoped ENNReal

theorem main_estimate : MainEstimate := by
  sorry

end TriangularHilbert

end

end OAI
