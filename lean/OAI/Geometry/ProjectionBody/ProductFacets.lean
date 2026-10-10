import OAI.Geometry.ProjectionBody.SimplexFacets
import Mathlib.Tactic.Tauto

namespace OAI

noncomputable section
open Set

namespace ProjectionCounterexample

def firstBlockLinear : E 20 →ₗ[ℝ] E 10 where
  toFun := firstBlock
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def secondBlockLinear : E 20 →ₗ[ℝ] E 10 where
  toFun := secondBlock
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The twenty-two bounding inequalities of the actual Cartesian product. -/
def productFunctional : Bool × Option (Fin 10) → E 20 →ₗ[ℝ] ℝ
  | (false, i) => (simplexFunctional 10 i).comp firstBlockLinear
  | (true, i) => (simplexFunctional 10 i).comp secondBlockLinear

def productLevel (i : Bool × Option (Fin 10)) : ℝ := simplexLevel i.2

@[simp] theorem productFunctional_first (i : Option (Fin 10)) (x : E 20) :
    productFunctional (false, i) x = simplexFunctional 10 i (firstBlock x) := rfl

@[simp] theorem productFunctional_second (i : Option (Fin 10)) (x : E 20) :
    productFunctional (true, i) x = simplexFunctional 10 i (secondBlock x) := rfl

theorem productBody_eq_halfspaceBody :
    productBody = halfspaceBody productFunctional productLevel := by
  ext x
  change (firstBlock x ∈ simplex 10 ∧ secondBlock x ∈ simplex 10) ↔ _
  rw [simplex_eq_halfspaceBody]
  constructor
  · rintro ⟨hx, hy⟩ ⟨b, i⟩
    cases b
    · exact hx i
    · exact hy i
  · intro hx
    exact ⟨fun i => hx (false, i), fun i => hx (true, i)⟩

theorem blocks_eq_zero_iff (x : E 20) :
    firstBlock x = 0 ∧ secondBlock x = 0 ↔ x = 0 := by
  constructor
  · rintro ⟨hfirst, hsecond⟩
    ext i
    refine Fin.addCases (n := 10) (m := 10) (fun j => ?_) (fun j => ?_) i
    · exact congrArg (fun y : E 10 => y j) hfirst
    · exact congrArg (fun y : E 10 => y j) hsecond
  · rintro rfl
    exact ⟨rfl, rfl⟩

theorem product_has_positive_slope {u : E 20} (hu : u ≠ 0) :
    ∃ i, 0 < productFunctional i u := by
  by_cases hfirst : firstBlock u = 0
  · have hsecond : secondBlock u ≠ 0 := by
      intro hsecond
      exact hu ((blocks_eq_zero_iff u).mp ⟨hfirst, hsecond⟩)
    obtain ⟨i, hi⟩ := simplex_has_positive_slope hsecond
    exact ⟨(true, i), hi⟩
  · obtain ⟨i, hi⟩ := simplex_has_positive_slope hfirst
    exact ⟨(false, i), hi⟩

theorem product_boundingFace_first (i : Option (Fin 10)) :
    boundingFace productFunctional productLevel (false, i) =
      {x | firstBlock x ∈ boundingFace (simplexFunctional 10) simplexLevel i ∧
        secondBlock x ∈ simplex 10} := by
  ext x
  simp only [boundingFace, ← productBody_eq_halfspaceBody, productBody,
    mem_ofPred_eq, productFunctional_first, productLevel, simplex_eq_halfspaceBody]
  tauto

theorem product_boundingFace_second (i : Option (Fin 10)) :
    boundingFace productFunctional productLevel (true, i) =
      {x | firstBlock x ∈ simplex 10 ∧
        secondBlock x ∈ boundingFace (simplexFunctional 10) simplexLevel i} := by
  ext x
  simp only [boundingFace, ← productBody_eq_halfspaceBody, productBody,
    mem_ofPred_eq, productFunctional_second, productLevel, simplex_eq_halfspaceBody]
  tauto

theorem product_functional_balance (u : E 20) :
    ∑ i, productFunctional i u = 0 := by
  simp [Fintype.sum_prod_type]

theorem product_absolute_slopes (u : E 20) :
    ∑ i, |productFunctional i u| =
      ((∑ i, |firstBlock u i|) + |∑ i, firstBlock u i|) +
      ((∑ i, |secondBlock u i|) + |∑ i, secondBlock u i|) := by
  simp [Fintype.sum_prod_type, add_comm]

end ProjectionCounterexample

end

end OAI
