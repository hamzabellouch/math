import Mathlib

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal ComplexInnerProductSpace
namespace ContinuousCircleWeight

abbrev CircleX := AddCircle (1:ℝ)

abbrev TracialHilbert := lp (fun _ : ℤ × ℤ => ℂ) 2
abbrev Operator := TracialHilbert →L[ℂ] TracialHilbert

def circleIdentification : CircleX ≃ₜ Circle :=
  AddCircle.homeomorphCircle (by norm_num)
def circleFunction (f : C(CircleX, ℝ)) (z : ℂ) : ℂ :=
  if hz : ‖z‖ = 1 then f (circleIdentification.symm ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩) else 0

def negativeLog (t : ℝ) : ℝ≥0∞ :=
  if t = 0 then ∞ else ENNReal.ofReal (-Real.log t)

structure IsTracialRotation (θ : ℝ) (U V : unitary Operator)
    (e : TracialHilbert) : Prop where
  relation : (V : Operator) * (U : Operator) =
    Complex.exp (2 * Real.pi * θ * Complex.I) • ((U : Operator) * (V : Operator))
  moments : ∀ m n : ℤ,
    inner ℂ e (((U ^ m * V ^ n : unitary Operator) : Operator) e) =
      if m = 0 ∧ n = 0 then 1 else 0
  cyclic : (Submodule.span ℂ
    (Set.range (fun mn : ℤ × ℤ =>
      ((U ^ mn.1 * V ^ mn.2 : unitary Operator) : Operator) e))).topologicalClosure = ⊤

def rotationAlgebra (U V : unitary Operator) : Set Operator :=
  Set.centralizer (Set.centralizer ({(U : Operator), (V : Operator)} : Set Operator))

def weightedRotation (U V : unitary Operator) (f : C(CircleX, ℝ)) : Operator :=
  (U : Operator) * cfc (circleFunction f) (V : Operator)

def MainStatement : Prop :=
  ∃ (θ : ℝ) (f : C(CircleX, ℝ)) (U V : unitary Operator) (e : TracialHilbert),
    0 < θ ∧ θ < 1 ∧ Irrational θ ∧
    IsTracialRotation θ U V e ∧
    (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
    (∃ z : CircleX, ∀ x, f x = 0 ↔ x = z) ∧
    (∫⁻ x, negativeLog (f x) ∂(volume : Measure CircleX)) = ∞ ∧
    ∀ p : Operator, p ∈ rotationAlgebra U V → IsStarProjection p →
      (1 - p) * weightedRotation U V f * p = 0 → p = 0 ∨ p = 1

theorem main_theorem : MainStatement := by
  sorry

end ContinuousCircleWeight
end

end OAI
