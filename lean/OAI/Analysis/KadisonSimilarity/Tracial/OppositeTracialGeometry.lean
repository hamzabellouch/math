import OAI.Analysis.KadisonSimilarity.Tracial.TracialBoundedBalls
import OAI.Analysis.KadisonSimilarity.Tracial.TracialCornerRepresentations

namespace OAI

/-! Right multiplication is the left representation of the opposite algebra.
This transfers the proved bounded-ball normality criterion to its actual range. -/

noncomputable section
namespace KadisonSimilarity.TracialCornerGeometry
open scoped CStarAlgebra

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

def rightRepresentation : Pᵐᵒᵖ →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun a := G.right (MulOpposite.unop a)
  map_zero' := by
    ext ξ
    refine G.dense_vector.induction_on ξ (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro a
    simp only [MulOpposite.unop_zero, right_vector, mul_zero, map_zero,
      zero_apply]
  map_one' := by
    ext ξ
    refine G.dense_vector.induction_on ξ (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro a
    simp only [MulOpposite.unop_one, right_vector, mul_one, one_apply_eq_self]
  map_add' a b := by
    ext ξ
    refine G.dense_vector.induction_on ξ (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro c
    simp only [MulOpposite.unop_add, right_vector, mul_add, map_add,
      add_apply]
  map_mul' a b := G.right_mul (MulOpposite.unop b) (MulOpposite.unop a)
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, MulOpposite.unop_smul, MulOpposite.unop_one]
    change G.right (z • (1 : P)) = z • (1 : H →L[ℂ] H)
    ext ξ
    refine G.dense_vector.induction_on ξ (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro a
    simp only [right_vector, mul_smul_comm, mul_one, map_smul,
      smul_apply, one_apply_eq_self]
  map_star' a := (G.right_adjoint (MulOpposite.unop a)).symm

@[simp] theorem rightRepresentation_apply (a : Pᵐᵒᵖ) :
    G.rightRepresentation a = G.right (MulOpposite.unop a) := rfl

def oppositeGeometry : TracialCornerGeometry Pᵐᵒᵖ H where
  trace := G.trace.comp (MulOpposite.opLinearEquiv ℂ).symm.toLinearMap
  vector := G.vector.comp (MulOpposite.opLinearEquiv ℂ).symm.toLinearMap
  left := G.rightRepresentation
  inner_vector a b := by
    change inner ℂ (G.vector (MulOpposite.unop a)) (G.vector (MulOpposite.unop b)) =
      G.trace (MulOpposite.unop b * star (MulOpposite.unop a))
    rw [G.inner_vector, G.tracial]
  tracial a b := G.tracial (MulOpposite.unop b) (MulOpposite.unop a)
  dense_vector := by
    intro ξ
    have hrange : Set.range (G.vector.comp (MulOpposite.opLinearEquiv ℂ).symm.toLinearMap) =
        Set.range G.vector := by
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨MulOpposite.unop a, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨MulOpposite.op a, rfl⟩
    change ξ ∈ closure (Set.range (G.vector.comp (MulOpposite.opLinearEquiv ℂ).symm.toLinearMap))
    rw [hrange]
    exact G.dense_vector ξ
  left_vector a b := G.right_vector (MulOpposite.unop b) (MulOpposite.unop a)

@[simp] theorem oppositeGeometry_vector (a : Pᵐᵒᵖ) :
    G.oppositeGeometry.vector a = G.vector (MulOpposite.unop a) := rfl

/-- The right range is a von Neumann algebra when the original left range is normal. -/
theorem rightRepresentation_normal_range (h1 : G.trace 1 = 1)
    (hf : Function.Injective G.vector) (M : VonNeumannAlgebra H)
    (hrange : G.left.range = M.toStarSubalgebra) :
    G.rightRepresentation.range =
      (representationVonNeumannAlgebra G.rightRepresentation).toStarSubalgebra := by
  apply G.oppositeGeometry.normal_range_of_closed_trace_balls
  intro C
  have h := G.trace_balls_closed_of_normal_range h1 hf M hrange C
  have heq : G.oppositeGeometry.vector '' Metric.closedBall (0 : Pᵐᵒᵖ) C =
      G.vector '' Metric.closedBall (0 : P) C := by
    ext ξ
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨MulOpposite.unop a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨MulOpposite.op a, ha, rfl⟩
  rwa [heq]

end KadisonSimilarity.TracialCornerGeometry

end

end OAI
