import OAI.Geometry.ProjectionBody.FacetCoordinates
import Mathlib.Tactic.Abel

namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

/-- A graph chart with one coordinate determined by a linear equation. -/
def graphLinear {n : ℕ} (i : Fin (n + 1)) (a : E n) : E n →ₗ[ℝ] E (n + 1) where
  toFun x := insertZero i x - ⟪a, x⟫ • EuclideanSpace.single i 1
  map_add' x y := by
    simp only [map_add, inner_add_right, add_smul]
    abel
  map_smul' c x := by
    simp only [map_smul, real_inner_smul_right, smul_sub, smul_smul, RingHom.id_apply]

/-- The corresponding unnormalized normal has coordinate `i` equal to one. -/
def graphNormal {n : ℕ} (i : Fin (n + 1)) (a : E n) : E (n + 1) :=
  insertZero i a + EuclideanSpace.single i 1

@[simp] theorem graphNormal_same {n : ℕ} (i : Fin (n + 1)) (a : E n) :
    graphNormal i a i = 1 := by simp [graphNormal]

theorem graphNormal_ne_zero {n : ℕ} (i : Fin (n + 1)) (a : E n) :
    graphNormal i a ≠ 0 := by
  intro h
  have := congrArg (fun x : E (n + 1) => x i) h
  simp at this

@[simp] theorem graphLinear_same {n : ℕ} (i : Fin (n + 1)) (a x : E n) :
    graphLinear i a x i = -⟪a, x⟫ := by simp [graphLinear]

@[simp] theorem graphLinear_succAbove {n : ℕ} (i : Fin (n + 1))
    (a x : E n) (j : Fin n) :
    graphLinear i a x (i.succAbove j) = x j := by simp [graphLinear]

theorem graphLinear_inner {n : ℕ} (i : Fin (n + 1)) (a x y : E n) :
    ⟪graphLinear i a x, graphLinear i a y⟫ = ⟪x, y⟫ + ⟪a, x⟫ * ⟪a, y⟫ := by
  simp [graphLinear, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right, (insertZero i).inner_map_map, mul_comm]

theorem graphNormal_inner_graphLinear {n : ℕ} (i : Fin (n + 1)) (a x : E n) :
    ⟪graphNormal i a, graphLinear i a x⟫ = 0 := by
  simp [graphNormal, graphLinear, inner_add_left, inner_sub_right,
    real_inner_smul_right, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right, (insertZero i).inner_map_map]

theorem graphNormal_norm_sq {n : ℕ} (i : Fin (n + 1)) (a : E n) :
    ‖graphNormal i a‖ ^ 2 = 1 + ‖a‖ ^ 2 := by
  calc
    ‖graphNormal i a‖ ^ 2 = ⟪graphNormal i a, graphNormal i a⟫ :=
      (real_inner_self_eq_norm_sq _).symm
    _ = 1 + ‖a‖ ^ 2 := by
      unfold graphNormal
      rw [inner_add_left, inner_add_right, inner_add_right]
      simp [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
        add_comm]

end ProjectionCounterexample

end

end OAI
