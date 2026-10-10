import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TensorProducts.SpatialFiniteMatrices
import OAI.Analysis.JiangSu.TraceCone.CompactDensity

namespace OAI

noncomputable section

attribute [local instance 2000] UnitalTomsWinter.stabilizationHilbertNormedAddCommGroup
  UnitalTomsWinter.stabilizationHilbertSeminormedAddCommGroup
  UnitalTomsWinter.stabilizationHilbertAddCommMonoid
  UnitalTomsWinter.stabilizationHilbertContinuousAdd
  UnitalTomsWinter.stabilizationHilbertModule
  UnitalTomsWinter.stabilizationHilbertInnerProductSpace
  UnitalTomsWinter.stabilizationHilbertNormedSpace

local instance (priority := 2000) directFastUnitalTomsWinterSpatialCompactTensorRing (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Ring (UnitalTomsWinter.StabilizationOperators H) := ContinuousLinearMap.ring
local instance (priority := 2000) directFastUnitalTomsWinterSpatialCompactTensorCStar (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    CStarAlgebra (UnitalTomsWinter.StabilizationOperators H) := instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace
local instance (priority := 2000) directFastUnitalTomsWinterSpatialCompactTensorSemiring (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Semiring (UnitalTomsWinter.StabilizationOperators H) := (directFastUnitalTomsWinterSpatialCompactTensorRing H).toSemiring
local instance (priority := 2000) directFastUnitalTomsWinterSpatialCompactTensorNonSemiring (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    NonUnitalSemiring (UnitalTomsWinter.StabilizationOperators H) := (directFastUnitalTomsWinterSpatialCompactTensorRing H).toNonUnitalSemiring
local instance (priority := 2000) directFastUnitalTomsWinterSpatialCompactTensorNonAssoc (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    NonUnitalNonAssocSemiring (UnitalTomsWinter.StabilizationOperators H) :=
  (directFastUnitalTomsWinterSpatialCompactTensorRing H).toNonUnitalNonAssocSemiring
local instance (priority := 2000) directFastUnitalTomsWinterSpatialCompactTensorAdd (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    AddMonoid (UnitalTomsWinter.StabilizationOperators H) := ContinuousLinearMap.instAddMonoid

open scoped CStarAlgebra Topology TensorProduct

namespace UnitalTomsWinter
open TraceCone

local instance : ContinuousStar StandardOperators where
  continuous_star :=
    (ContinuousLinearMap.adjoint : StandardOperators ≃ₗᵢ⋆[ℂ] StandardOperators).continuous

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))

def spatialCompactAlgebra : NonUnitalStarSubalgebra ℂ (StabilizationOperators H) :=
  (NonUnitalStarAlgebra.adjoin ℂ {R | ∃ (a : A) (T : StandardCompacts),
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
  exact NonUnitalStarSubalgebra.le_topologicalClosure _
    (NonUnitalStarAlgebra.subset_adjoin ℂ _ ⟨n,M,rfl⟩)

def spatialTensorRight (S : H →L[ℂ] H) : StandardOperators →L[ℂ] StabilizationOperators H :=
  LinearMap.mkContinuous
    { toFun := spatialTensorOp S
      map_add' := spatialTensorOp_add_right S
      map_smul' := fun c T => spatialTensorOp_smul_right c S T }
    ‖S‖ (fun T => spatialTensorOp_norm_le S T)

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
    have he : spatialTensorOp (π a) (T*S) = spatialTensorOp (π a) T * spatialTensorOp (π 1) S := by
      rw [← spatialTensorOp_mul, ← map_mul, mul_one]
    rw [he]
    exact (spatialMatrixAlgebra π).mul_mem (hT a) (hS 1)

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
    · apply NonUnitalStarAlgebra.adjoin_le
      rintro R ⟨n,M,rfl⟩
      exact spatialFinite_mem_compactAlgebra π n M
    · exact NonUnitalStarSubalgebra.isClosed_topologicalClosure _

variable [PartialOrder A] [StarOrderedRing A]

theorem spatialRepresentation_range_compact (hπ : Function.Injective π) :
    Set.range (spatialRepresentation π) = (spatialCompactAlgebra π : Set (StabilizationOperators H)) := by
  rw [spatialCompactAlgebra_eq_matrixAlgebra, spatialRepresentation_range π hπ]
end UnitalTomsWinter
end

end OAI
