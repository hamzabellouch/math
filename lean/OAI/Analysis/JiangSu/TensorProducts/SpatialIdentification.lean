import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.MatrixAlgebras.SharedMatrixBridge
import OAI.Analysis.JiangSu.TensorProducts.SpatialCompactTensor
import OAI.Analysis.JiangSu.MatrixAlgebras.MatrixUnitCorners
import OAI.Analysis.JiangSu.CStarAlgebras.FaithfulGNS

namespace OAI

attribute [local instance 2000] UnitalTomsWinter.stabilizationHilbertNormedAddCommGroup
  UnitalTomsWinter.stabilizationHilbertSeminormedAddCommGroup
  UnitalTomsWinter.stabilizationHilbertAddCommMonoid
  UnitalTomsWinter.stabilizationHilbertContinuousAdd
  UnitalTomsWinter.stabilizationHilbertModule
  UnitalTomsWinter.stabilizationHilbertInnerProductSpace
  UnitalTomsWinter.stabilizationHilbertNormedSpace

noncomputable section

local instance (priority := 2000) stabilizationOperatorsAddCommGroup
    (Hilbert : Type*) [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert] :
    AddCommGroup (UnitalTomsWinter.StabilizationOperators Hilbert) :=
  ContinuousLinearMap.addCommGroup

section

local instance (priority := 2000) directFastUnitalTomsWinterSpatialIdentificationRing (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Ring (UnitalTomsWinter.StabilizationOperators H) := ContinuousLinearMap.ring
local instance (priority := 2000) directFastUnitalTomsWinterSpatialIdentificationCStar (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    CStarAlgebra (UnitalTomsWinter.StabilizationOperators H) := instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace
local instance (priority := 2000) directFastUnitalTomsWinterSpatialIdentificationSemiring (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Semiring (UnitalTomsWinter.StabilizationOperators H) := (directFastUnitalTomsWinterSpatialIdentificationRing H).toSemiring
local instance (priority := 2000) directFastUnitalTomsWinterSpatialIdentificationNonSemiring (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    NonUnitalSemiring (UnitalTomsWinter.StabilizationOperators H) := (directFastUnitalTomsWinterSpatialIdentificationRing H).toNonUnitalSemiring
local instance (priority := 2000) directFastUnitalTomsWinterSpatialIdentificationNonAssoc (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    NonUnitalNonAssocSemiring (UnitalTomsWinter.StabilizationOperators H) :=
  (directFastUnitalTomsWinterSpatialIdentificationRing H).toNonUnitalNonAssocSemiring
local instance (priority := 2000) directFastUnitalTomsWinterSpatialIdentificationAdd (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    AddMonoid (UnitalTomsWinter.StabilizationOperators H) := ContinuousLinearMap.instAddMonoid

open scoped CStarAlgebra Topology

namespace UnitalTomsWinter
open TraceCone

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))

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

def spatialStage (n : ℕ) : FinMatrix A n →⋆ₙₐ[ℂ] SpatialStabilization π :=
  (spatialRepresentationInto π).comp (matrixLimitStage n)

lemma spatialStage_eq_equiv (hπ : Function.Injective π) (n : ℕ) (M : FinMatrix A n) :
    spatialStage π n M = spatialEquiv π hπ (matrixLimitStage n M) := rfl

@[simp] theorem spatialStage_coe (n : ℕ) (M : FinMatrix A n) :
    (spatialStage π n M : StabilizationOperators H) = spatialFinite π n M :=
  spatialRepresentation_stage π n M

theorem spatialStage_isometry (hπ : Function.Injective π) (n : ℕ) : Isometry (spatialStage π n) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro M
  change ‖spatialRepresentation π (matrixLimitStage n M)‖ = ‖M‖
  rw [spatialRepresentation_norm π hπ, matrixLimitStage_norm]

private theorem transport_full_corner {D E F : Type*}
    [NonUnitalCStarAlgebra D] [NonUnitalCStarAlgebra E] [CStarAlgebra F]
    (f : D →⋆ₙₐ[ℂ] E) (hf : Function.Bijective f) (ι : F →⋆ₙₐ[ℂ] D)
    (hc : ∀ x : D, ι 1 * x * ι 1 = x → ∃ a : F, ι a = x)
    (x : E) (hx : (f.comp ι) 1 * x * (f.comp ι) 1 = x) :
    ∃ a : F, (f.comp ι) a = x := by
  obtain ⟨y,rfl⟩ := hf.2 x
  have he (a : F) : (f.comp ι) a = f (ι a) := rfl
  rw [he] at hx
  have hy : ι 1 * y * ι 1 = y := hf.1 (by simpa only [map_mul] using hx)
  obtain ⟨a,ha⟩ := hc y hy
  exact ⟨a,congrArg f ha⟩

theorem spatialStage_full_corner (hπ : Function.Injective π) (n : ℕ) (x : SpatialStabilization π)
    (hx : spatialStage π n 1 * x * spatialStage π n 1 = x) :
    ∃ M : FinMatrix A n, spatialStage π n M = x := by
  have hb : Function.Bijective (spatialRepresentationInto π) := by
    change Function.Bijective (spatialEquiv π hπ)
    exact (spatialEquiv π hπ).bijective
  exact transport_full_corner (spatialRepresentationInto π) hb (matrixLimitStage n)
    (matrixLimitStage_full_corner n) x hx

theorem cuntzSubequiv_reflect_spatial (hπ : Function.Injective π) {n : ℕ} {a b : FinMatrix A n}
    (h : CuntzSubequiv (spatialStage π n a) (spatialStage π n b)) : CuntzSubequiv a b :=
  CuntzSubequiv.reflect_corner (spatialStage π n) (spatialStage_isometry π hπ n).injective
    (spatialStage_full_corner π hπ n) h

def TracialState.spatialEquiv [IsSimpleCStarAlgebra A] (τ : TracialState A) :
    MatrixLimit A ≃⋆ₐ[ℂ] SpatialStabilization τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom :=
  UnitalTomsWinter.spatialEquiv τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom τ.gns_injective
end UnitalTomsWinter
end


local instance (priority := 2000) directFastCompletedSpatialBridgeRing (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Ring (UnitalTomsWinter.StabilizationOperators H) := ContinuousLinearMap.ring
local instance (priority := 2000) directFastCompletedSpatialBridgeCStar (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    CStarAlgebra (UnitalTomsWinter.StabilizationOperators H) := instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace
local instance (priority := 2000) directFastCompletedSpatialBridgeSemiring (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Semiring (UnitalTomsWinter.StabilizationOperators H) := (directFastCompletedSpatialBridgeRing H).toSemiring
local instance (priority := 2000) directFastCompletedSpatialBridgeNonSemiring (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    NonUnitalSemiring (UnitalTomsWinter.StabilizationOperators H) := (directFastCompletedSpatialBridgeRing H).toNonUnitalSemiring
local instance (priority := 2000) directFastCompletedSpatialBridgeNonAssoc (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    NonUnitalNonAssocSemiring (UnitalTomsWinter.StabilizationOperators H) :=
  (directFastCompletedSpatialBridgeRing H).toNonUnitalNonAssocSemiring
local instance (priority := 2000) directFastCompletedSpatialBridgeAdd (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    AddMonoid (UnitalTomsWinter.StabilizationOperators H) := ContinuousLinearMap.instAddMonoid

open scoped CStarAlgebra

namespace Pureness
variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : Function.Injective π)

def completedSpatialEquiv : CornerCompletion A ≃⋆ₐ[ℂ] UnitalTomsWinter.SpatialStabilization π :=
  sharedMatrixEquiv.symm.trans (UnitalTomsWinter.spatialEquiv π hπ)

@[simp] theorem completedSpatialEquiv_stage (k : ℕ) (a : MatrixStage A k) :
    completedSpatialEquiv π hπ (completedMatrixInclude A k a) =
      UnitalTomsWinter.spatialStage π k a := by
  have hx : sharedMatrixEquiv.symm (completedMatrixInclude A k a) = TraceCone.matrixLimitStage k a :=
    (congrArg sharedMatrixEquiv.symm (sharedMatrixEquiv_stage k a).symm).trans
      (sharedMatrixEquiv.symm_apply_apply _)
  exact congrArg (UnitalTomsWinter.spatialEquiv π hπ) hx

@[simp] theorem completedSpatialEquiv_norm (x : CornerCompletion A) :
    ‖completedSpatialEquiv π hπ x‖ = ‖x‖ := by
  change ‖UnitalTomsWinter.spatialEquiv π hπ (sharedMatrixEquiv.symm x)‖ = ‖x‖
  rw [UnitalTomsWinter.spatialEquiv_norm]
  exact (sharedMatrixToCompletion_norm (sharedMatrixEquiv.symm x)).symm.trans
    (congrArg norm (sharedMatrixEquiv.apply_symm_apply x))

theorem completedSpatialEquiv_cut (k : ℕ) (x : CornerCompletion A) :
    completedSpatialEquiv π hπ (completedCornerCut A k x) =
      UnitalTomsWinter.spatialStage π k 1 * completedSpatialEquiv π hπ x *
        UnitalTomsWinter.spatialStage π k 1 := by
  simp only [completedCornerCut, completedProjection, map_mul, completedSpatialEquiv_stage]

def TracialState.toShared (τ : TracialState A) : UnitalTomsWinter.TracialState A where
  toPositiveLinearMap := τ.functional
  normalized := τ.normalized
  tracial := τ.tracial

theorem TracialState.source_gns_injective (τ : TracialState A) (hsimple : TopologicallySimple A) :
    Function.Injective τ.functional.gnsNonUnitalStarAlgHom := by
  apply UnitalTomsWinter.faithful_gns_injective τ.functional
  intro a ha
  exact (CStarRing.star_mul_self_eq_zero_iff a).mp
    (τ.faithful hsimple (star a*a) (star_mul_self_nonneg a) ha)

def TracialState.completedSpatialEquiv (τ : TracialState A) (hsimple : TopologicallySimple A) :
    CornerCompletion A ≃⋆ₐ[ℂ]
      UnitalTomsWinter.SpatialStabilization τ.functional.gnsNonUnitalStarAlgHom :=
  Pureness.completedSpatialEquiv τ.functional.gnsNonUnitalStarAlgHom (τ.source_gns_injective hsimple)

end Pureness

end

end OAI
