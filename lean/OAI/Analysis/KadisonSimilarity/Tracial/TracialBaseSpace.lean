import OAI.Analysis.KadisonSimilarity.Representation.CStarCorner
import OAI.Analysis.KadisonSimilarity.OperatorAlgebra

namespace OAI

/-! The completed base Hilbert space of a represented tracial star algebra,
its actual inclusion, and compression of the ambient left action. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

/-- The algebraic vectors coming from the specified star subalgebra. -/
def baseAlgebraVectors : A →ₗ[ℂ] H := G.vector.comp A.subtype.toLinearMap

@[simp] theorem baseAlgebraVectors_apply (a : A) :
    G.baseAlgebraVectors A a = G.vector (a : P) := rfl

/-- The actual closed base subspace, with no independent density input. -/
def baseSpace : ClosedSubmodule ℂ H := (G.baseAlgebraVectors A).range.closure

instance baseSpace_complete : CompleteSpace (G.baseSpace A).toSubmodule :=
  (G.baseSpace A).isClosed.completeSpace_coe

/-- The dense algebra-vector map into its Hilbert completion. -/
def baseVector : A →ₗ[ℂ] G.baseSpace A :=
  (G.baseAlgebraVectors A).codRestrict (G.baseSpace A).toSubmodule fun a =>
    (G.baseAlgebraVectors A).range.le_topologicalClosure ⟨a, rfl⟩

@[simp] theorem baseVector_coe (a : A) :
    (G.baseVector A a : H) = G.vector (a : P) := rfl

theorem baseVector_dense : DenseRange (G.baseVector A) := by
  change Dense (Set.range (G.baseVector A))
  rw [Subtype.dense_iff, ← Set.range_comp]
  change closure (Set.range (G.baseAlgebraVectors A)) ⊆
    closure (Set.range (G.baseAlgebraVectors A))
  exact Set.Subset.rfl

/-- The canonical isometry from the completed base into the ambient space. -/
def baseInclusion : G.baseSpace A →ₗᵢ[ℂ] H := (G.baseSpace A).toSubmodule.subtypeₗᵢ

@[simp] theorem baseInclusion_apply (x : G.baseSpace A) : G.baseInclusion A x = (x : H) := rfl

@[simp] theorem baseInclusion_vector (a : A) :
    G.baseInclusion A (G.baseVector A a) = G.vector (a : P) := rfl

theorem baseInclusion_adjoint :
    (G.baseInclusion A).toContinuousLinearMap.adjoint =
      (G.baseSpace A).toSubmodule.orthogonalProjectionOnto :=
  (G.baseSpace A).toSubmodule.adjoint_subtypeL

theorem baseInclusion_adjoint_self :
    (G.baseInclusion A).toContinuousLinearMap.adjoint.comp
      (G.baseInclusion A).toContinuousLinearMap = ContinuousLinearMap.id ℂ (G.baseSpace A) := by
  have h := (G.baseInclusion A).adjoint_comp_self
  exact h

/-- Compression of an ambient bounded operator to the completed base. -/
def baseOperator (Y : H →L[ℂ] H) : G.baseSpace A →L[ℂ] G.baseSpace A :=
  (G.baseInclusion A).toContinuousLinearMap.adjoint.comp
    (Y.comp (G.baseInclusion A).toContinuousLinearMap)

@[simp] theorem baseOperator_adjoint (Y : H →L[ℂ] H) :
    (G.baseOperator A Y).adjoint = G.baseOperator A Y.adjoint := by
  simp only [baseOperator, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]

/-- The actual compressed left action on arbitrary ambient algebra elements. -/
def baseCompression : P →ₗ[ℂ] (G.baseSpace A →L[ℂ] G.baseSpace A) where
  toFun x := G.baseOperator A (G.left x)
  map_add' x y := by
    simp only [map_add, baseOperator, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.comp_add]
  map_smul' c x := by
    simp only [map_smul, baseOperator, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul, RingHom.id_apply]

@[simp] theorem baseCompression_apply (x : P) :
    G.baseCompression A x = G.baseOperator A (G.left x) := rfl

theorem baseCompression_one : G.baseCompression A 1 = ContinuousLinearMap.id ℂ (G.baseSpace A) := by
  change (G.baseInclusion A).toContinuousLinearMap.adjoint.comp
    ((G.left 1).comp (G.baseInclusion A).toContinuousLinearMap) = _
  rw [map_one, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
    G.baseInclusion_adjoint_self]

/-- The coefficient formula required by the tracial Fourier compression. -/
theorem baseCompression_inner (a b : A) (x : P) :
    inner ℂ (G.baseVector A a) (G.baseCompression A x (G.baseVector A b)) =
      G.trace (star (a : P) * x * (b : P)) := by
  change inner ℂ (G.baseVector A a)
    ((G.baseInclusion A).toContinuousLinearMap.adjoint
      (G.left x ((G.baseInclusion A).toContinuousLinearMap (G.baseVector A b)))) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (G.vector (a : P)) (G.left x (G.vector (b : P))) = _
  rw [G.left_vector, G.inner_vector, mul_assoc]

/-- The base Hilbert inner product is the original tracial one. -/
theorem baseVector_inner (a b : A) :
    inner ℂ (G.baseVector A a) (G.baseVector A b) =
      G.trace (star (a : P) * (b : P)) := G.inner_vector _ _

/-- Left multiplication by the subalgebra preserves the completed base. -/
theorem baseSpace_invariant (a : A) (x : H) (hx : x ∈ G.baseSpace A) :
    G.left (a : P) x ∈ G.baseSpace A := by
  have hm : Set.MapsTo (G.left (a : P))
      ((G.baseAlgebraVectors A).range : Set H) ((G.baseAlgebraVectors A).range : Set H) := by
    rintro y ⟨b, rfl⟩
    refine ⟨a * b, ?_⟩
    change G.vector ((a : P) * (b : P)) = G.left (a : P) (G.vector (b : P))
    rw [G.left_vector]
  exact hm.closure (G.left (a : P)).continuous hx

def baseAction (a : A) : G.baseSpace A →L[ℂ] G.baseSpace A :=
  (G.left (a : P)).restrict (G.baseSpace_invariant A a)

@[simp] theorem baseAction_coe (a : A) (x : G.baseSpace A) :
    (G.baseAction A a x : H) = G.left (a : P) (x : H) := rfl

/-- The restriction to the star subalgebra is a genuine unital star
representation on the completed base space. -/
def baseRepresentation : A →⋆ₐ[ℂ] (G.baseSpace A →L[ℂ] G.baseSpace A) where
  toFun := G.baseAction A
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
    change inner ℂ (y : H) (G.left (star (a : P)) (x : H)) =
      inner ℂ y ((G.baseAction A a).adjoint x)
    rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (y : H) (G.left (star (a : P)) (x : H)) =
      inner ℂ (G.left (a : P) (y : H)) (x : H)
    rw [map_star]
    exact ContinuousLinearMap.adjoint_inner_right _ _ _

@[simp] theorem baseRepresentation_coe (a : A) (x : G.baseSpace A) :
    (G.baseRepresentation A a x : H) = G.left (a : P) (x : H) := rfl

theorem baseInclusion_intertwines (a : A) :
    (G.left (a : P)).comp (G.baseInclusion A).toContinuousLinearMap =
      (G.baseInclusion A).toContinuousLinearMap.comp (G.baseRepresentation A a) := rfl

theorem baseCompression_subalgebra (a : A) :
    G.baseCompression A (a : P) = G.baseRepresentation A a := by
  change (G.baseInclusion A).toContinuousLinearMap.adjoint.comp
    ((G.left (a : P)).comp (G.baseInclusion A).toContinuousLinearMap) = _
  rw [G.baseInclusion_intertwines, ← ContinuousLinearMap.comp_assoc,
    G.baseInclusion_adjoint_self, ContinuousLinearMap.id_comp]

/-- Preservation of the base subspace gives the actual compressed
intertwining identity. -/
theorem baseOperator_intertwines (Y : H →L[ℂ] H)
    (hY : ∀ x ∈ G.baseSpace A, Y x ∈ G.baseSpace A) :
    Y.comp (G.baseInclusion A).toContinuousLinearMap =
      (G.baseInclusion A).toContinuousLinearMap.comp (G.baseOperator A Y) := by
  ext x
  change Y (x : H) = (G.baseInclusion A)
    ((G.baseInclusion A).toContinuousLinearMap.adjoint (Y (x : H)))
  rw [G.baseInclusion_adjoint]
  change Y (x : H) = (G.baseSpace A).toSubmodule.starProjection (Y (x : H))
  exact (Submodule.starProjection_eq_self_iff.mpr (hY x x.property)).symm

/-- A reducing base subspace makes the compressed commutator exactly the
compression of the ambient commutator. -/
theorem baseCompression_commutator (Y : H →L[ℂ] H)
    (hY : ∀ x ∈ G.baseSpace A, Y x ∈ G.baseSpace A)
    (hYstar : ∀ x ∈ G.baseSpace A, Y.adjoint x ∈ G.baseSpace A) (x : P) :
    commutator (G.baseOperator A Y) (G.baseCompression A x) =
      G.baseOperator A (commutator Y (G.left x)) := by
  have h := compression_commutator_identity Y (G.left x) (G.baseOperator A Y)
    (G.baseInclusion A).toContinuousLinearMap
  rw [G.baseOperator_intertwines A Y hY,
    G.baseOperator_intertwines A Y.adjoint hYstar, ← G.baseOperator_adjoint] at h
  simpa only [baseCompression_apply, baseOperator, sub_self, map_zero, ContinuousLinearMap.zero_comp,
    ContinuousLinearMap.comp_zero, sub_zero, add_zero] using h

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
