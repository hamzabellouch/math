import Mathlib

namespace OAI

namespace C0Absorption

open scoped ZeroAtInfty

abbrev C0 := C₀(ℕ, ℝ)

def BiLip {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
    ∀ x y, c * dist x y ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ C * dist x y

def NoLinearC0 (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z] : Prop :=
  ∀ T : C0 →L[ℝ] Z, ¬ ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ ‖T x‖

def MetricUniversal (Z : Type*) [MetricSpace Z] : Prop :=
  ∀ (M : Type) [MetricSpace M] [TopologicalSpace.SeparableSpace M],
    ∃ f : M → Z, BiLip f

def MainConclusion : Prop :=
  ∃ (Z : Type) (_ : NormedAddCommGroup Z) (_ : NormedSpace ℝ Z),
    CompleteSpace Z ∧ TopologicalSpace.SeparableSpace Z ∧ NoLinearC0 Z ∧
    (∃ F : Z × C0 → Z, Function.Surjective F ∧ BiLip F) ∧
    (∃ f : C0 → Z, BiLip f) ∧ MetricUniversal Z ∧
    ¬ Nonempty ((Z × C0) ≃L[ℝ] Z)

theorem main_result : MainConclusion := by sorry

end C0Absorption

end OAI
