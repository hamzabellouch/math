import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TensorProducts.SpatialIdentification

namespace OAI

attribute [-instance] Pureness.CStarAlgebraNorm.completionCStarAlgebra
noncomputable section
open scoped InnerProductSpace ComplexOrder TensorProduct

local instance (priority := 2000) spatialHilbertFastNonunitalSpatialGroup (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    NormedAddCommGroup (UnitalTomsWinter.StabilizationHilbert H) :=
  @UniformSpace.Completion.instNormedAddCommGroup (H ⊗[ℂ] TraceCone.StandardHilbert)
    TensorProduct.instNormedAddCommGroup.toSeminormedAddCommGroup
local instance (priority := 2000) spatialHilbertFastNonunitalSpatialSemi (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    SeminormedAddCommGroup (UnitalTomsWinter.StabilizationHilbert H) :=
  (spatialHilbertFastNonunitalSpatialGroup H).toSeminormedAddCommGroup
local instance (priority := 2000) spatialHilbertFastNonunitalSpatialInner (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    InnerProductSpace ℂ (UnitalTomsWinter.StabilizationHilbert H) :=
  UniformSpace.Completion.innerProductSpace
local instance (priority := 2000) nonunitalSpatialInlineNonunitalSpatialRing (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Ring (UnitalTomsWinter.StabilizationOperators H) := ContinuousLinearMap.ring
local instance (priority := 2000) nonunitalSpatialInlineNonunitalSpatialCStar (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    CStarAlgebra (UnitalTomsWinter.StabilizationOperators H) := instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace
local instance (priority := 2000) nonunitalSpatialInlineNonunitalSpatialSemiring (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Semiring (UnitalTomsWinter.StabilizationOperators H) := (nonunitalSpatialInlineNonunitalSpatialRing H).toSemiring
local instance (priority := 2000) nonunitalSpatialInlineNonunitalSpatialNonSemiring (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    NonUnitalSemiring (UnitalTomsWinter.StabilizationOperators H) := (nonunitalSpatialInlineNonunitalSpatialRing H).toNonUnitalSemiring
local instance (priority := 2000) nonunitalSpatialInlineNonunitalSpatialNonAssoc (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    NonUnitalNonAssocSemiring (UnitalTomsWinter.StabilizationOperators H) :=
  (nonunitalSpatialInlineNonunitalSpatialRing H).toNonUnitalNonAssocSemiring
local instance (priority := 2000) nonunitalSpatialInlineNonunitalSpatialAdd (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    AddMonoid (UnitalTomsWinter.StabilizationOperators H) := ContinuousLinearMap.instAddMonoid

local instance (priority := 2000) nonunitalSpatialOperatorsAddCommGroup
    (Hilbert : Type*) [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert] :
    AddCommGroup (UnitalTomsWinter.StabilizationOperators Hilbert) :=
  ContinuousLinearMap.addCommGroup

open scoped CStarAlgebra Topology TensorProduct

namespace NonunitalGamma.Spatial
open UnitalTomsWinter
open TraceCone

local instance : ContinuousStar StandardOperators where
  continuous_star :=
    (ContinuousLinearMap.adjoint : StandardOperators ≃ₗᵢ⋆[ℂ] StandardOperators).continuous

variable {A H : Type*} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : CStarAlgebra (StabilizationOperators H) :=
  UnitalTomsWinter.stabilizationOperatorsCStar

variable (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))

def spatialCompactAlgebra : NonUnitalStarSubalgebra ℂ (StabilizationOperators H) :=
  (NonUnitalStarAlgebra.adjoin ℂ {R : StabilizationOperators H | ∃ (a : A) (T : StandardCompacts),
    R = spatialTensorOp (π a) (T : StandardOperators)}).topologicalClosure

lemma spatialFinite_mem_compactAlgebra (n : ℕ) (M : FinMatrix A n) :
    spatialFinite π n M ∈ spatialCompactAlgebra π := by
  change (∑ i : Fin n, ∑ j : Fin n, spatialEntry π i.val j.val (M i j)) ∈ spatialCompactAlgebra π
  apply (spatialCompactAlgebra π).sum_mem
  intro i _
  apply (spatialCompactAlgebra π).sum_mem
  intro j _
  exact NonUnitalStarSubalgebra.le_topologicalClosure _
    (NonUnitalStarAlgebra.subset_adjoin ℂ _ ⟨M i j,compactMatrixUnit i j,rfl⟩)

lemma spatialEntry_mem_matrixAlgebra (i j : ℕ) (a : A) :
    spatialEntry π i j a ∈ spatialMatrixAlgebra π := by
  let n := max i j + 1
  let I : Fin n := ⟨i, Nat.lt_succ_of_le (le_max_left _ _)⟩
  let J : Fin n := ⟨j, Nat.lt_succ_of_le (le_max_right _ _)⟩
  let M : FinMatrix A n := CStarMatrix.ofMatrix (Matrix.single I J a)
  have hm : spatialFinite π n M = spatialEntry π i j a := by
    simp [spatialFinite, spatialFiniteValue, spatialMatrixSum, M, Matrix.single, I, J, ite_and, apply_ite]
  rw [← hm]
  apply NonUnitalStarSubalgebra.le_topologicalClosure
    (NonUnitalStarAlgebra.adjoin ℂ {R : StabilizationOperators H | ∃ n M,R=spatialFinite π n M})
  exact NonUnitalStarAlgebra.subset_adjoin ℂ _ ⟨n,M,rfl⟩

def spatialTensorRight (S : H →L[ℂ] H) : StandardOperators →L[ℂ] StabilizationOperators H :=
  LinearMap.mkContinuous
    { toFun := spatialTensorOp S
      map_add' := spatialTensorOp_add_right S
      map_smul' := fun c T => spatialTensorOp_smul_right c S T }
    ‖S‖ (fun T => spatialTensorOp_norm_le S T)

variable [PartialOrder A] [StarOrderedRing A]

lemma spatialTensor_matrixUnitAlgebra (T : StandardOperators) (hT : T ∈ matrixUnitAlgebra) :
    ∀ a : A, spatialTensorOp (π a) T ∈ spatialMatrixAlgebra π := by
  induction hT using NonUnitalStarAlgebra.adjoin_induction with
  | mem T hT =>
    obtain ⟨i,j,rfl⟩ := hT
    exact spatialEntry_mem_matrixAlgebra π i j
  | zero => intro a; simp
  | add T S _ _ hT hS =>
    intro a
    rw [spatialTensorOp_add_right]
    exact (spatialMatrixAlgebra π).add_mem (hT a) (hS a)
  | smul c T _ hT =>
    intro a
    rw [spatialTensorOp_smul_right]
    exact (spatialMatrixAlgebra π).smul_mem c (hT a)
  | star T _ hT =>
    intro a
    have he : spatialTensorOp (π a) (star T) = star (spatialTensorOp (π (star a)) T) := by
      rw [← spatialTensorOp_star, ← map_star, star_star]
    rw [he]
    exact star_mem (hT (star a))
  | mul T S _ _ hT hS =>
    intro a
    let L : (H →L[ℂ] H) →L[ℂ] StabilizationOperators H :=
      LinearMap.mkContinuous
        { toFun := fun R => spatialTensorOp R (T*S)
          map_add' := fun R Q => spatialTensorOp_add_left R Q (T*S)
          map_smul' := fun c R => spatialTensorOp_smul_left c R (T*S) }
        ‖T*S‖ (fun R => by
          change ‖spatialTensorOp R (T*S)‖ ≤ ‖T*S‖*‖R‖
          simpa only [mul_comm] using spatialTensorOp_norm_le R (T*S))
    have hπc : LipschitzWith 1 π := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul] using
        NonUnitalStarAlgHom.norm_apply_le π (x-y)
    have ht := L.continuous.tendsto (π a) |>.comp
      (hπc.continuous.tendsto a |>.comp
        ((CStarAlgebra.increasingApproximateUnit A).tendsto_mul_left a))
    apply (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).mem_of_tendsto ht
    apply Filter.Eventually.of_forall
    intro e
    change spatialTensorOp (π (a*e)) (T*S) ∈ spatialMatrixAlgebra π
    rw [map_mul,spatialTensorOp_mul]
    exact (spatialMatrixAlgebra π).mul_mem (hT a) (hS e)

theorem spatialTensor_compact_mem (a : A) (T : StandardCompacts) :
    spatialTensorOp (π a) (T : StandardOperators) ∈ spatialMatrixAlgebra π := by
  have ht : (T : StandardOperators) ∈ matrixUnitAlgebra.topologicalClosure := by
    rw [matrixUnitClosure_eq_compactOperatorAlgebra]
    exact T.2
  have hc : IsClosed {S : StandardOperators | spatialTensorOp (π a) S ∈ spatialMatrixAlgebra π} :=
    (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).preimage (spatialTensorRight (π a)).continuous
  apply closure_minimal ?_ hc ht
  intro S hS
  exact spatialTensor_matrixUnitAlgebra π S hS a

theorem spatialCompactAlgebra_eq_matrixAlgebra : spatialCompactAlgebra π = spatialMatrixAlgebra π := by
  apply le_antisymm
  · apply NonUnitalStarSubalgebra.topologicalClosure_minimal
    · apply NonUnitalStarAlgebra.adjoin_le
      rintro R ⟨a,T,rfl⟩
      exact spatialTensor_compact_mem π a T
    · exact NonUnitalStarSubalgebra.isClosed_topologicalClosure _
  · apply NonUnitalStarSubalgebra.topologicalClosure_minimal
    · apply NonUnitalStarAlgebra.adjoin_le (A := StabilizationOperators H)
      rintro R ⟨n,M,rfl⟩
      exact spatialFinite_mem_compactAlgebra π n M
    · exact NonUnitalStarSubalgebra.isClosed_topologicalClosure _

theorem spatialRepresentation_range_compact (hπ : Function.Injective π) :
    Set.range (spatialRepresentation π) = (spatialCompactAlgebra π : Set (StabilizationOperators H)) := by
  rw [spatialCompactAlgebra_eq_matrixAlgebra, spatialRepresentation_range π hπ]
instance spatialCompactAlgebra_closed : IsClosed (spatialCompactAlgebra π : Set (StabilizationOperators H)) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

abbrev SpatialStabilization := spatialCompactAlgebra π

instance : NonUnitalCStarAlgebra (SpatialStabilization π) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (spatialCompactAlgebra π)

def spatialRepresentationInto : MatrixLimit A →⋆ₙₐ[ℂ] SpatialStabilization π where
  toFun x := ⟨spatialRepresentation π x, by
    change spatialRepresentation π x ∈ spatialCompactAlgebra π
    rw [spatialCompactAlgebra_eq_matrixAlgebra]
    exact spatialRepresentation_mem π x⟩
  map_zero' := Subtype.ext (spatialRepresentation π).map_zero'
  map_add' x y := Subtype.ext (map_add (spatialRepresentation π) x y)
  map_mul' x y := Subtype.ext (map_mul (spatialRepresentation π) x y)
  map_smul' c x := Subtype.ext (map_smul (spatialRepresentation π) c x)
  map_star' x := Subtype.ext (map_star (spatialRepresentation π) x)

def spatialEquiv (hπ : Function.Injective π) : MatrixLimit A ≃⋆ₐ[ℂ] SpatialStabilization π :=
  StarAlgEquiv.ofBijective (spatialRepresentationInto π) ⟨
    fun x y h => (spatialRepresentation_isometry π hπ).injective (congrArg Subtype.val h),
    fun T => by
      have ht : T.1 ∈ Set.range (spatialRepresentation π) := by
        rw [spatialRepresentation_range_compact π hπ]
        exact T.2
      obtain ⟨x,hx⟩ := ht
      exact ⟨x,Subtype.ext hx⟩⟩

@[simp] theorem spatialEquiv_norm (hπ : Function.Injective π) (x : MatrixLimit A) :
    ‖spatialEquiv π hπ x‖ = ‖x‖ := spatialRepresentation_norm π hπ x

end NonunitalGamma.Spatial

end

end OAI
