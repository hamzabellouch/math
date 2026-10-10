import OAI.Analysis.KadisonSimilarity.Tracial.TracialCornerRepresentations
import OAI.Analysis.KadisonSimilarity.Tracial.MatrixUnitCoordinates

namespace OAI

/-! Support projections and represented right columns in a concrete tracial
Hilbert space. These are the ambient spaces used by the full-column lemma. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H)

@[simp] theorem right_one : G.right 1 = ContinuousLinearMap.id ℂ H := by
  apply ContinuousLinearMap.ext
  intro x
  refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  simp

@[simp] theorem right_zero : G.right 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  simp

theorem cornerProjection_adjoint (e r : P) (he : IsStarProjection e) (hr : IsStarProjection r) :
    (G.cornerProjection e r).adjoint = G.cornerProjection e r := by
  rw [cornerProjection, ContinuousLinearMap.adjoint_comp, G.right_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint, ← map_star,
    he.isSelfAdjoint.star_eq, hr.isSelfAdjoint.star_eq]
  exact G.right_left e r

/-- The support-equation projection is the actual orthogonal projection
onto the completed two-sided Hilbert corner. -/
theorem cornerInto_eq_adjoint (e r : P) (he : IsStarProjection e) (hr : IsStarProjection r) :
    G.cornerInto e r he.isIdempotentElem hr.isIdempotentElem =
      (G.corner e r).toSubmodule.subtypeL.adjoint := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (y : H) (G.cornerProjection e r x) = inner ℂ (y : H) x
  rw [← G.cornerProjection_adjoint e r he hr,
    ContinuousLinearMap.adjoint_inner_right]
  have hfix := congrArg (fun z : G.corner e r => (z : H))
    (G.cornerInto_self e r he.isIdempotentElem hr.isIdempotentElem y)
  change G.cornerProjection e r y = (y : H) at hfix
  rw [hfix]

theorem corner_inclusion_adjoint (e r : P) (he : IsStarProjection e) (hr : IsStarProjection r) :
    (G.corner e r).toSubmodule.subtypeL.comp
      (G.corner e r).toSubmodule.subtypeL.adjoint = G.cornerProjection e r := by
  rw [← G.cornerInto_eq_adjoint e r he hr]
  rfl

theorem rightColumn_mem (r a : P) (x : H) (hx : x ∈ G.corner 1 r) :
    G.left a x ∈ G.corner 1 r := by
  rw [G.mem_corner] at hx ⊢
  constructor
  · simp
  · have hc := congrArg (fun T : H →L[ℂ] H => T x) (G.right_left a r)
    simpa only [ContinuousLinearMap.comp_apply, hx.2] using hc

def rightColumnAction (r a : P) : G.corner 1 r →L[ℂ] G.corner 1 r :=
  (G.left a).restrict (G.rightColumn_mem r a)

@[simp] theorem rightColumnAction_coe (r a : P) (x : G.corner 1 r) :
    (G.rightColumnAction r a x : H) = G.left a x := rfl

/-- Left multiplication by the full algebra on a right-supported Hilbert
column. No standard-form representation theorem is used here. -/
def rightColumnRepresentation (r : P) : P →⋆ₐ[ℂ] (G.corner 1 r →L[ℂ] G.corner 1 r) where
  toFun := G.rightColumnAction r
  map_zero' := by ext x; simp
  map_one' := by ext x; simp
  map_add' a b := by ext x; simp
  map_mul' a b := by ext x; simp [mul_apply_eq_comp]
  commutes' c := by ext x; simp [Algebra.algebraMap_eq_smul_one]
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ (y : H) (G.left (star a) (x : H)) =
      inner ℂ y ((G.rightColumnAction r a).adjoint x)
    rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (y : H) (G.left (star a) (x : H)) =
      inner ℂ (G.left a (y : H)) (x : H)
    rw [map_star]
    exact ContinuousLinearMap.adjoint_inner_right _ _ _

@[simp] theorem rightColumnRepresentation_coe (r a : P) (x : G.corner 1 r) :
    (G.rightColumnRepresentation r a x : H) = G.left a x := rfl

theorem rightColumn_inclusion_intertwines (r a : P) :
    (G.left a).comp (G.corner 1 r).toSubmodule.subtypeL =
      (G.corner 1 r).toSubmodule.subtypeL.comp (G.rightColumnRepresentation r a) := rfl

/-- The adjoint of the inclusion is the right support projection and is a
left-module map; this supplies the projection data of the full-column lemma. -/
theorem rightColumn_projection (r : P) (hr : IsStarProjection r) :
    (G.corner 1 r).toSubmodule.subtypeL.comp
      (G.corner 1 r).toSubmodule.subtypeL.adjoint = G.right r := by
  rw [G.corner_inclusion_adjoint 1 r (IsStarProjection.one P) hr]
  simp [cornerProjection, ContinuousLinearMap.one_def]

theorem rightColumn_adjoint_intertwines (r a : P) :
    (G.corner 1 r).toSubmodule.subtypeL.adjoint.comp (G.left a) =
      (G.rightColumnRepresentation r a).comp (G.corner 1 r).toSubmodule.subtypeL.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint (G.rightColumn_inclusion_intertwines r (star a))
  simpa only [ContinuousLinearMap.adjoint_comp, map_star,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint] using h

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
