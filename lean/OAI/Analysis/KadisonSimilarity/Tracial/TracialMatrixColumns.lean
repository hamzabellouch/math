import OAI.Analysis.KadisonSimilarity.Tracial.TracialCornerEstimate
import OAI.Analysis.KadisonSimilarity.Tracial.MatrixCornerFrames

namespace OAI

/-! The matrix-unit column coordinates of a concrete tracial corner. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (e : P) (he : IsStarProjection e) (r : P)

/-- Forget only the left support of a two-sided corner. -/
def cornerToRightColumn : G.corner e r →ₗᵢ[ℂ] G.corner 1 r where
  toFun x := ⟨x, by
    rw [G.mem_corner]
    exact ⟨by simp, ((G.mem_corner e r x).mp x.property).2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

@[simp] theorem cornerToRightColumn_coe (x : G.corner e r) :
    (G.cornerToRightColumn e r x : H) = x := rfl

theorem cornerToRightColumn_adjoint (hr : IsStarProjection r) (x : G.corner 1 r) :
    (G.cornerToRightColumn e r).toContinuousLinearMap.adjoint x =
      G.cornerInto e r he.isIdempotentElem hr.isIdempotentElem (x : H) := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right, G.cornerInto_eq_adjoint e r he hr,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

include he in
theorem cornerToRightColumn_projection (hr : IsStarProjection r) :
    (G.cornerToRightColumn e r).toContinuousLinearMap.comp
      (G.cornerToRightColumn e r).toContinuousLinearMap.adjoint =
        G.rightColumnRepresentation r e := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  rw [ContinuousLinearMap.comp_apply, G.cornerToRightColumn_adjoint e he r hr]
  change G.left e (G.right r (x : H)) = G.left e (x : H)
  rw [((G.mem_corner 1 r x).mp x.property).2]

/-- The finite range decomposition in the ambient Hilbert space. -/
def ambientCornerColumns {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then e else 0)
    (hsum : ∑ i, v i * star (v i) = 1) :
    FiniteOrthogonalColumns (G.corner e 1) H n :=
  partialIsometryColumns G.left e he v hv hsum (G.corner e 1).toSubmodule.subtypeₗᵢ (by
    change (G.corner e 1).toSubmodule.subtypeL.comp
      (G.corner e 1).toSubmodule.subtypeL.adjoint = G.left e
    rw [G.corner_inclusion_adjoint e 1 he (IsStarProjection.one P), cornerProjection,
      G.right_one, ContinuousLinearMap.comp_id])

/-- The same finite range decomposition in the right-supported column. -/
def supportedCornerColumns (hr : IsStarProjection r) {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then e else 0)
    (hsum : ∑ i, v i * star (v i) = 1) :
    FiniteOrthogonalColumns (G.corner e r) (G.corner 1 r) n :=
  partialIsometryColumns (G.rightColumnRepresentation r) e he v hv hsum
    (G.cornerToRightColumn e r) (G.cornerToRightColumn_projection e he r hr)

/-- Matrix entries of an arbitrary algebra element, as actual elements of
the unital corner algebra. -/
def cornerMatrixEntry {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then e else 0)
    (a : P) (i j : Fin n) : CStarCorner e he :=
  ⟨star (v i) * a * v j, by
    have hi : e * star (v i) = star (v i) := by
      have h := congrArg star (mul_initial_projection e (v i) he (by simpa using hv i i))
      simpa only [star_mul, star_star, he.isSelfAdjoint.star_eq] using h
    have hj := mul_initial_projection e (v j) he (by simpa using hv j j)
    constructor
    · rw [← mul_assoc, ← mul_assoc, hi]
    · rw [mul_assoc, hj]⟩

theorem cornerRepresentation_compression (a : CStarCorner e he) :
    G.cornerRepresentation e he 1 a =
      (G.corner e 1).toSubmodule.subtypeL.adjoint.comp
        ((G.left (a : P)).comp (G.corner e 1).toSubmodule.subtypeL) := by
  rw [G.corner_inclusion_intertwines e he 1 a, ← ContinuousLinearMap.comp_assoc]
  have hI : (G.corner e 1).toSubmodule.subtypeL.adjoint.comp
      (G.corner e 1).toSubmodule.subtypeL = 1 :=
    (G.corner e 1).toSubmodule.subtypeₗᵢ.adjoint_comp_self
  change _ = ((G.corner e 1).toSubmodule.subtypeL.adjoint.comp
    (G.corner e 1).toSubmodule.subtypeL).comp _
  rw [hI, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

theorem cornerRepresentation_supported_compression (a : CStarCorner e he) :
    G.cornerRepresentation e he r a =
      (G.cornerToRightColumn e r).toContinuousLinearMap.adjoint.comp
        ((G.rightColumnRepresentation r (a : P)).comp
          (G.cornerToRightColumn e r).toContinuousLinearMap) := by
  have hi : (G.rightColumnRepresentation r (a : P)).comp
      (G.cornerToRightColumn e r).toContinuousLinearMap =
      (G.cornerToRightColumn e r).toContinuousLinearMap.comp
        (G.cornerRepresentation e he r a) := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  rw [hi, ← ContinuousLinearMap.comp_assoc,
    (G.cornerToRightColumn e r).adjoint_comp_self, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_comp]

/-- The ambient matrix coordinate entries are the actual elements
`vᵢ* a vⱼ` of `ePe`. -/
theorem ambientCornerColumns_entry {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then e else 0)
    (hsum : ∑ i, v i * star (v i) = 1) (a : P) (i j : Fin n) :
    G.cornerRepresentation e he 1 (cornerMatrixEntry e he v hv a i j) =
      ((G.ambientCornerColumns e he v hv hsum).inclusion i).adjoint.comp
        ((G.left a).comp ((G.ambientCornerColumns e he v hv hsum).inclusion j)) := by
  rw [G.cornerRepresentation_compression]
  exact (partialIsometryColumns_entry G.left e he v hv hsum
    (G.corner e 1).toSubmodule.subtypeₗᵢ _ a i j).symm

theorem supportedCornerColumns_entry (hr : IsStarProjection r) {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then e else 0)
    (hsum : ∑ i, v i * star (v i) = 1) (a : P) (i j : Fin n) :
    G.cornerRepresentation e he r (cornerMatrixEntry e he v hv a i j) =
      ((G.supportedCornerColumns e he r hr v hv hsum).inclusion i).adjoint.comp
        ((G.rightColumnRepresentation r a).comp
          ((G.supportedCornerColumns e he r hr v hv hsum).inclusion j)) := by
  rw [G.cornerRepresentation_supported_compression]
  exact (partialIsometryColumns_entry (G.rightColumnRepresentation r) e he v hv hsum
    (G.cornerToRightColumn e r) _ a i j).symm

/-- Both coordinate unitaries and every entry in the full-column theorem
are now constructed from the same finite family in the tracial algebra. -/
def fullColumnCoordinates (hr : IsStarProjection r) {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then e else 0)
    (hsum : ∑ i, v i * star (v i) = 1) :
    FullColumnCoordinates G.left (G.rightColumnRepresentation r)
      (G.cornerRepresentation e he 1) (G.cornerRepresentation e he r) n :=
  fullColumnCoordinatesOfColumns G.left (G.rightColumnRepresentation r)
    (G.cornerRepresentation e he 1) (G.cornerRepresentation e he r)
    (G.ambientCornerColumns e he v hv hsum)
    (G.supportedCornerColumns e he r hr v hv hsum)
    (cornerMatrixEntry e he v hv)
    (G.ambientCornerColumns_entry e he v hv hsum)
    (G.supportedCornerColumns_entry e he r hr v hv hsum)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
