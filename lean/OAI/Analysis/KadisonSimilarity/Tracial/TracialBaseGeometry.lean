import OAI.Analysis.KadisonSimilarity.Tracial.TracialBaseSpace

namespace OAI

/-! The closed base algebra has its actual tracial Hilbert representation
inside the ambient one. Its left, right, and conjugation actions are compatible
with the canonical base inclusion. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

/-- Completeness in the inherited subtype norm supplies the closedness needed
for Mathlib's subtype C-star algebra instance. -/
theorem baseAlgebra_isClosed_of_complete [CompleteSpace A] : IsClosed (A : Set P) :=
  (completeSpace_coe_iff_isComplete.mp (inferInstance : CompleteSpace A)).isClosed

variable [IsClosed (A : Set P)]

/-- Restrict the trace and left action to the closed base algebra; the Hilbert
space is the closure of its actual ambient algebra vectors. -/
def baseGeometry : TracialCornerGeometry A (G.baseSpace A) where
  trace := G.trace.comp A.subtype.toLinearMap
  vector := G.baseVector A
  left := G.baseRepresentation A
  inner_vector a b := G.baseVector_inner A a b
  tracial a b := G.tracial (a : P) (b : P)
  dense_vector := G.baseVector_dense A
  left_vector a b := by
    apply Subtype.ext
    change G.left (a : P) (G.vector (b : P)) = G.vector ((a : P) * (b : P))
    exact G.left_vector (a : P) (b : P)

@[simp] theorem baseGeometry_trace (a : A) :
    (G.baseGeometry A).trace a = G.trace (a : P) := rfl

@[simp] theorem baseGeometry_vector_coe (a : A) :
    ((G.baseGeometry A).vector a : H) = G.vector (a : P) := rfl

@[simp] theorem baseGeometry_left_coe (a : A) (x : G.baseSpace A) :
    ((G.baseGeometry A).left a x : H) = G.left (a : P) (x : H) := rfl

/-- The actual base trace is normalized whenever the ambient trace is. -/
theorem baseGeometry_trace_one (htrace : G.trace 1 = 1) :
    (G.baseGeometry A).trace 1 = 1 := htrace

/-- Faithfulness of the represented algebra vectors passes to the base. -/
theorem baseGeometry_vector_injective (hfaithful : Function.Injective G.vector) :
    Function.Injective (G.baseGeometry A).vector := by
  intro a b hab
  apply Subtype.ext
  apply hfaithful
  exact congrArg (fun x : G.baseSpace A => (x : H)) hab

/-- The tracial conjugation of the base is exactly the restriction of ambient
tracial conjugation, proved on the dense algebra vectors. -/
theorem baseGeometry_conjugation_coe (x : G.baseSpace A) :
    ((G.baseGeometry A).conjugation x : H) = G.conjugation (x : H) := by
  refine (G.baseVector_dense A).induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  change ((G.baseGeometry A).conjugation ((G.baseGeometry A).vector a) : H) =
    G.conjugation (G.vector (a : P))
  rw [TracialCornerGeometry.conjugation_vector, G.conjugation_vector]
  rfl

/-- Base right multiplication is the restriction of actual ambient right
multiplication. No independent commutation representation is assumed. -/
theorem baseGeometry_right_coe (a : A) (x : G.baseSpace A) :
    ((G.baseGeometry A).right a x : H) = G.right (a : P) (x : H) := by
  refine (G.baseVector_dense A).induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  change ((G.baseGeometry A).right a ((G.baseGeometry A).vector b) : H) =
    G.right (a : P) (G.vector (b : P))
  rw [TracialCornerGeometry.right_vector, G.right_vector]
  rfl

/-- The completed base subspace is invariant under right multiplication by
its algebra, with membership derived from the constructed base geometry. -/
theorem baseSpace_right_invariant (a : A) (x : H) (hx : x ∈ G.baseSpace A) :
    G.right (a : P) x ∈ G.baseSpace A := by
  rw [← G.baseGeometry_right_coe A a (⟨x, hx⟩ : G.baseSpace A)]
  exact ((G.baseGeometry A).right a (⟨x, hx⟩ : G.baseSpace A)).property

/-- Operator form of the exact right-action inclusion. -/
theorem baseGeometry_right_intertwines (a : A) :
    (G.baseInclusion A).toContinuousLinearMap.comp ((G.baseGeometry A).right a) =
      (G.right (a : P)).comp (G.baseInclusion A).toContinuousLinearMap := by
  ext x
  exact G.baseGeometry_right_coe A a x

/-- Compression of an ambient base-algebra right multiplier is its actual
right action in the completed base representation. -/
theorem baseGeometry_right_compression (a : A) :
    G.baseOperator A (G.right (a : P)) = (G.baseGeometry A).right a := by
  change (G.baseInclusion A).toContinuousLinearMap.adjoint.comp
    ((G.right (a : P)).comp (G.baseInclusion A).toContinuousLinearMap) = _
  rw [← G.baseGeometry_right_intertwines A a, ← ContinuousLinearMap.comp_assoc,
    G.baseInclusion_adjoint_self, ContinuousLinearMap.id_comp]

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
