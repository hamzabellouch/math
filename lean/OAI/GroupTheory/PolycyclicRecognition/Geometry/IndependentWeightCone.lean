import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConePolarTemplate
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PositiveWeightCones
import Mathlib.LinearAlgebra.LinearIndependent.Defs

namespace OAI

/-! # The closed cones used by the neighboring-offset argument

A ray and a cone on two independent weights are closed. We construct them
as actual proper cones, so polar separation requires no closedness input.
-/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {I : Type*} [Fintype I]

/-- The nonnegative span of an independent finite family is closed. -/
def independentWeightCone (v : I → V) (hv : LinearIndependent ℝ v) : ProperCone ℝ V where
  toSubmodule := (PointedCone.positive ℝ (I → ℝ)).map (Fintype.linearCombination ℝ v)
  isClosed' := by
    have he := LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr
        (linearIndependent_iff_injective_fintypeLinearCombination.mp hv))
    exact he.isClosedMap _ isClosed_Ici

@[simp] theorem mem_independentWeightCone (v : I → V) (hv : LinearIndependent ℝ v)
    (x : V) : x ∈ independentWeightCone v hv ↔
      ∃ a : I → ℝ, (∀ i, 0 ≤ a i) ∧ ∑ i, a i • v i = x := by
  rfl

def closedWeightRay (α : V) (hα : α ≠ 0) : ProperCone ℝ V :=
  independentWeightCone (fun _ : Fin 1 => α) (by
    simpa using (linearIndependent_unique_iff (R := ℝ) (v := fun _ : Fin 1 => α)).mpr hα)

@[simp] theorem mem_closedWeightRay {α : V} (hα : α ≠ 0) (β : V) :
    β ∈ closedWeightRay α hα ↔ ∃ c : ℝ, 0 ≤ c ∧ β = c • α := by
  simp only [closedWeightRay, mem_independentWeightCone, Fin.sum_univ_one]
  constructor
  · rintro ⟨a, ha, he⟩
    exact ⟨a 0, ha 0, he.symm⟩
  · rintro ⟨c, hc, he⟩
    exact ⟨fun _ => c, fun _ => hc, he.symm⟩

theorem closedWeightRay_eq_insert {α : V} (hα : α ≠ 0) :
    (closedWeightRay α hα : Set V) = insert 0 (positiveWeightRay α) := by
  ext β
  change β ∈ closedWeightRay α hα ↔ β ∈ insert 0 (positiveWeightRay α)
  rw [mem_closedWeightRay]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain rfl | hc := eq_or_lt_of_le hc
    · simp
    · exact mem_insert_of_mem _ ⟨c, hc, rfl⟩
  · rintro (rfl | ⟨c, hc, rfl⟩)
    · exact ⟨0, le_rfl, by simp⟩
    · exact ⟨c, hc.le, rfl⟩

def closedTwoWeightCone (α η : V) (h : LinearIndependent ℝ ![α, η]) : ProperCone ℝ V :=
  independentWeightCone ![α, η] h

@[simp] theorem mem_closedTwoWeightCone (α η : V) (h : LinearIndependent ℝ ![α, η])
    (β : V) : β ∈ closedTwoWeightCone α η h ↔
      ∃ c d : ℝ, 0 ≤ c ∧ 0 ≤ d ∧ β = c • α + d • η := by
  simp only [closedTwoWeightCone, mem_independentWeightCone, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨a, ha, he⟩
    exact ⟨a 0, a 1, ha 0, ha 1, he.symm⟩
  · rintro ⟨c, d, hc, hd, he⟩
    refine ⟨![c, d], ?_, he.symm⟩
    intro i
    fin_cases i <;> assumption

theorem closedTwoWeightCone_eq_insert (α η : V) (h : LinearIndependent ℝ ![α, η]) :
    (closedTwoWeightCone α η h : Set V) = insert 0 (positiveWeightCone α η) := by
  ext β
  change β ∈ closedTwoWeightCone α η h ↔ β ∈ insert 0 (positiveWeightCone α η)
  rw [mem_closedTwoWeightCone]
  constructor
  · rintro ⟨c, d, hc, hd, rfl⟩
    by_cases he : c + d = 0
    · have hc0 : c = 0 := by linarith
      have hd0 : d = 0 := by linarith
      simp [hc0, hd0]
    · exact mem_insert_of_mem _ ⟨c, d, hc, hd, lt_of_le_of_ne (add_nonneg hc hd) (Ne.symm he), rfl⟩
  · rintro (rfl | ⟨c, d, hc, hd, _, he⟩)
    · exact ⟨0, 0, le_rfl, le_rfl, by simp⟩
    · exact ⟨c, d, hc, hd, he⟩

end PolycyclicRecognition

end

end OAI
