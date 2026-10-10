import OAI.Analysis.KadisonSimilarity.Representation.CStarCorner

namespace OAI

/-! Actual corner representations on the completed tracial Hilbert corners. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (e : P) (he : IsStarProjection e) (r : P)

instance cornerSubmodule_complete : CompleteSpace (G.corner e r).toSubmodule :=
  (G.corner e r).isClosed.completeSpace_coe

/-- Left multiplication by a corner element preserves both support equations. -/
theorem cornerAction_mem (a : CStarCorner e he) (x : H) (hx : x ∈ G.corner e r) :
    G.left (a : P) x ∈ G.corner e r := by
  rw [G.mem_corner] at hx ⊢
  constructor
  · have ha := congrArg (fun b : P => G.left b x) a.property.1
    simpa only [map_mul, mul_apply_eq_comp] using ha
  · have h := congrArg (fun T : H →L[ℂ] H => T x) (G.right_left (a : P) r)
    simpa only [ContinuousLinearMap.comp_apply, hx.2] using h

def cornerAction (a : CStarCorner e he) : G.corner e r →L[ℂ] G.corner e r :=
  (G.left (a : P)).restrict (G.cornerAction_mem e he r a)

@[simp] theorem cornerAction_coe (a : CStarCorner e he) (x : G.corner e r) :
    (G.cornerAction e he r a x : H) = G.left (a : P) x := rfl

/-- The identity of `ePe` is `e`, acting as the identity on `eL²(P)r`. -/
def cornerRepresentation : CStarCorner e he →⋆ₐ[ℂ] (G.corner e r →L[ℂ] G.corner e r) where
  toFun := G.cornerAction e he r
  map_zero' := by
    ext x
    simp
  map_one' := by
    ext x
    change G.left ((1 : CStarCorner e he) : P) (x : H) = x
    rw [CStarCorner.coe_one]
    exact ((G.mem_corner e r x).mp x.property).1
  map_add' a b := by
    ext x
    change G.left ((a : P) + (b : P)) (x : H) = _
    simp
  map_mul' a b := by
    ext x
    change G.left ((a : P) * (b : P)) (x : H) = _
    simp [mul_apply_eq_comp]
  commutes' c := by
    ext x
    change G.left ((algebraMap ℂ (CStarCorner e he) c : CStarCorner e he) : P) (x : H) = _
    rw [Algebra.algebraMap_eq_smul_one]
    change G.left (c • ((1 : CStarCorner e he) : P)) (x : H) = _
    rw [CStarCorner.coe_one, map_smul]
    change c • G.left e (x : H) = c • (x : H)
    rw [((G.mem_corner e r x).mp x.property).1]
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ (y : H) (G.left (star (a : P)) (x : H)) =
      inner ℂ y ((G.cornerAction e he r a).adjoint x)
    rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (y : H) (G.left (star (a : P)) (x : H)) =
      inner ℂ (G.left (a : P) (y : H)) (x : H)
    rw [map_star]
    exact ContinuousLinearMap.adjoint_inner_right _ _ _

@[simp] theorem cornerRepresentation_coe (a : CStarCorner e he) (x : G.corner e r) :
    (G.cornerRepresentation e he r a x : H) = G.left (a : P) x := rfl

theorem corner_inclusion_intertwines (a : CStarCorner e he) :
    (G.left (a : P)).comp (G.corner e r).toSubmodule.subtypeL =
      (G.corner e r).toSubmodule.subtypeL.comp (G.cornerRepresentation e he r a) := rfl

theorem corner_adjoint_intertwines (a : CStarCorner e he) :
    (G.corner e r).toSubmodule.subtypeL.adjoint.comp (G.left (a : P)) =
      (G.cornerRepresentation e he r a).comp (G.corner e r).toSubmodule.subtypeL.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint (G.corner_inclusion_intertwines e he r (star a))
  have hL : G.left ((star a : CStarCorner e he) : P) = (G.left (a : P)).adjoint := by
    change G.left (star (a : P)) = _
    rw [map_star, ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.adjoint_comp, hL, ContinuousLinearMap.adjoint_adjoint] at h
  simpa only [ContinuousLinearMap.adjoint_comp, map_star,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint] using h

/-- The geometric cyclicity result now applies to the actual algebra `ePe`
and its actual left representation, with no abstract-coordinate hypotheses. -/
theorem cornerRepresentation_cyclic (hr : IsStarProjection r) (v : P)
    (hv : star v * v = r) (hev : e * (v * star v) = v * star v) :
    CyclicStarRepresentation (G.cornerRepresentation e he r) :=
  tracial_corner_cyclic_of_partial_isometry G e r he hr
    (G.cornerRepresentation e he r) Subtype.val (CStarCorner.full e he)
    (fun _ _ => rfl) v hv hev

/-- Faithfulness of the dense tracial algebra vectors makes right
multiplication faithful, as required by the full-column theorem. -/
def faithfulRightAction (hV : Function.Injective G.vector) :
    TracialRightAction (P := P) (H := H) where
  right := G.right
  injective := by
    intro a b hab
    apply hV
    have h := congrArg (fun T : H →L[ℂ] H => T (G.vector 1)) hab
    simpa only [G.right_vector, one_mul] using h
  mul := G.right_mul

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
