import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.MatrixCorners
import OAI.Analysis.JiangSu.TraceCone.CompactOperators

namespace OAI


noncomputable section
open scoped TensorProduct InnerProductSpace CStarAlgebra
open UniformSpace.Completion

namespace UnitalTomsWinter
open TraceCone

variable {A H : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
abbrev StabilizationHilbert (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  SpatialHilbert H StandardHilbert

local instance (priority := 2000) stabilizationHilbertNormedAddCommGroup
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    NormedAddCommGroup (StabilizationHilbert H) :=
  @UniformSpace.Completion.instNormedAddCommGroup (H ⊗[ℂ] StandardHilbert)
    TensorProduct.instNormedAddCommGroup.toSeminormedAddCommGroup
local instance (priority := 2000) stabilizationHilbertSeminormedAddCommGroup
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    SeminormedAddCommGroup (StabilizationHilbert H) :=
  (stabilizationHilbertNormedAddCommGroup H).toSeminormedAddCommGroup
local instance (priority := 2000) stabilizationHilbertAddCommMonoid
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    AddCommMonoid (StabilizationHilbert H) :=
  (stabilizationHilbertNormedAddCommGroup H).toAddCommMonoid
local instance (priority := 2000) stabilizationHilbertContinuousAdd
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    ContinuousAdd (StabilizationHilbert H) :=
  (SeminormedAddCommGroup.toIsTopologicalAddGroup
    (E := StabilizationHilbert H)).toContinuousAdd
local instance (priority := 2000) stabilizationHilbertModule
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Module ℂ (StabilizationHilbert H) := UniformSpace.Completion.instModule
local instance (priority := 2000) stabilizationHilbertInnerProductSpace
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    InnerProductSpace ℂ (StabilizationHilbert H) := UniformSpace.Completion.innerProductSpace
local instance (priority := 2000) stabilizationHilbertNormedSpace
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    NormedSpace ℂ (StabilizationHilbert H) :=
  (stabilizationHilbertInnerProductSpace H).toNormedSpace

abbrev StabilizationOperators (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  StabilizationHilbert H →L[ℂ] StabilizationHilbert H

local instance (priority := 2000) directFastUnitalTomsWinterSpatialFiniteMatricesRing (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Ring (UnitalTomsWinter.StabilizationOperators H) := ContinuousLinearMap.ring
local instance (priority := 2000) directFastUnitalTomsWinterSpatialFiniteMatricesCStar (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    CStarAlgebra (UnitalTomsWinter.StabilizationOperators H) := instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace
local instance (priority := 2000) directFastUnitalTomsWinterSpatialFiniteMatricesSemiring (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Semiring (UnitalTomsWinter.StabilizationOperators H) := (directFastUnitalTomsWinterSpatialFiniteMatricesRing H).toSemiring
local instance (priority := 2000) directFastUnitalTomsWinterSpatialFiniteMatricesNonSemiring (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    NonUnitalSemiring (UnitalTomsWinter.StabilizationOperators H) := (directFastUnitalTomsWinterSpatialFiniteMatricesRing H).toNonUnitalSemiring
local instance (priority := 2000) directFastUnitalTomsWinterSpatialFiniteMatricesNonAssoc (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    NonUnitalNonAssocSemiring (UnitalTomsWinter.StabilizationOperators H) :=
  (directFastUnitalTomsWinterSpatialFiniteMatricesRing H).toNonUnitalNonAssocSemiring
local instance (priority := 2000) directFastUnitalTomsWinterSpatialFiniteMatricesAdd (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    AddMonoid (UnitalTomsWinter.StabilizationOperators H) := ContinuousLinearMap.instAddMonoid

def spatialEntry (i j : ℕ) (a : A) : StabilizationOperators H :=
  spatialTensorOp (π a) (compactMatrixUnit i j : StandardHilbert →L[ℂ] StandardHilbert)

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma spatialEntry_zero (i j : ℕ) : spatialEntry π i j 0 = 0 := by simp [spatialEntry]
omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma spatialEntry_add (i j : ℕ) (a b : A) :
    spatialEntry π i j (a+b) = spatialEntry π i j a + spatialEntry π i j b := by
  simp [spatialEntry, spatialTensorOp_add_left]
omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma spatialEntry_smul (i j : ℕ) (c : ℂ) (a : A) :
    spatialEntry π i j (c • a) = c • spatialEntry π i j a := by
  simp [spatialEntry, spatialTensorOp_smul_left]
omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma spatialEntry_star (i j : ℕ) (a : A) :
    star (spatialEntry π i j a) = spatialEntry π j i (star a) := by
  rw [spatialEntry, ← spatialTensorOp_star, ← map_star]
  congr 1
  exact congrArg Subtype.val (compactMatrixUnit_star i j)
omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma spatialEntry_mul (i j k l : ℕ) (a b : A) :
    spatialEntry π i j a * spatialEntry π k l b =
      if j=k then spatialEntry π i l (a*b) else 0 := by
  rw [spatialEntry, spatialEntry, ← spatialTensorOp_mul, ← map_mul]
  have h := congrArg Subtype.val (compactMatrixUnit_mul i j k l)
  change (compactMatrixUnit i j : StandardHilbert →L[ℂ] StandardHilbert) *
    (compactMatrixUnit k l : StandardHilbert →L[ℂ] StandardHilbert) = _ at h
  rw [h]
  split_ifs <;> simp_all [spatialEntry]

omit [PartialOrder A] [StarOrderedRing A] in
lemma spatialEntry_sum {ι : Type*} (s : Finset ι) (i j : ℕ) (f : ι → A) :
    spatialEntry π i j (∑ k ∈ s, f k) = ∑ k ∈ s, spatialEntry π i j (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih => simp [hk,ih]

def spatialMatrixSum {n : ℕ} (M : Fin n → Fin n → A) : StabilizationOperators H :=
  ∑ i : Fin n, ∑ j : Fin n, spatialEntry π i.val j.val (M i j)

omit [PartialOrder A] [StarOrderedRing A] in
lemma spatialMatrixSum_star {n : ℕ} (M : Fin n → Fin n → A) :
    spatialMatrixSum π (fun i j => star (M j i)) = star (spatialMatrixSum π M) := by
  unfold spatialMatrixSum
  rw [_root_.star_sum (R := StabilizationOperators H)]
  simp only [_root_.star_sum, spatialEntry_star]
  exact Finset.sum_comm

omit [PartialOrder A] [StarOrderedRing A] in
lemma spatialMatrixSum_mul {n : ℕ} (M N : Fin n → Fin n → A) :
    spatialMatrixSum π (fun i j => ∑ k, M i k * N k j) = spatialMatrixSum π M * spatialMatrixSum π N := by
  simp only [spatialMatrixSum, spatialEntry_sum, Finset.sum_mul,
    Finset.mul_sum, spatialEntry_mul, Fin.val_inj]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_comm

def spatialFiniteValue (n : ℕ) (M : FinMatrix A n) : StabilizationOperators H :=
  spatialMatrixSum π (fun i j => M i j)

omit [PartialOrder A] [StarOrderedRing A] in
lemma spatialFiniteValue_star (n : ℕ) (M : FinMatrix A n) :
    spatialFiniteValue π n (star M) = star (spatialFiniteValue π n M) :=
  spatialMatrixSum_star π (fun i j => M i j)

omit [PartialOrder A] [StarOrderedRing A] in
lemma spatialFiniteValue_mul (n : ℕ) (M N : FinMatrix A n) :
    spatialFiniteValue π n (M*N) = spatialFiniteValue π n M * spatialFiniteValue π n N :=
  spatialMatrixSum_mul π (fun i j => M i j) (fun i j => N i j)

def spatialFinite (n : ℕ) : FinMatrix A n →⋆ₙₐ[ℂ] StabilizationOperators H where
  toFun := spatialFiniteValue π n
  map_zero' := by simp [spatialFiniteValue, spatialMatrixSum]
  map_add' M N := by simp [spatialFiniteValue, spatialMatrixSum, Finset.sum_add_distrib]
  map_smul' c M := by simp [spatialFiniteValue, spatialMatrixSum, Finset.smul_sum]
  map_star' := spatialFiniteValue_star π n
  map_mul' := spatialFiniteValue_mul π n

omit [PartialOrder A] [StarOrderedRing A] in
lemma spatialFinite_coefficient (n : ℕ) (M : FinMatrix A n) (i j : Fin n) (x y : H) :
    inner ℂ (spatialFinite π n M (x ⊗ₜ[ℂ] standardVector j.val : H ⊗[ℂ] StandardHilbert))
      (y ⊗ₜ[ℂ] standardVector i.val : H ⊗[ℂ] StandardHilbert) = inner ℂ (π (M i j) x) y := by
  simp [spatialFinite, spatialFiniteValue, spatialMatrixSum, spatialEntry, compactMatrixUnit, InnerProductSpace.rankOne_apply,
    inner_standardVector, sum_inner, Fin.val_inj, apply_ite, coe_zero]

omit [PartialOrder A] [StarOrderedRing A] in
theorem spatialFinite_injective (hπ : Function.Injective π) (n : ℕ) :
    Function.Injective (spatialFinite π n) := by
  intro M N he
  apply CStarMatrix.ext; intro i j
  apply hπ
  apply ContinuousLinearMap.ext; intro x
  apply ext_inner_right ℂ
  intro y
  rw [← spatialFinite_coefficient π n M i j x y, ← spatialFinite_coefficient π n N i j x y, he]

 theorem spatialFinite_isometry (hπ : Function.Injective π) (n : ℕ) : Isometry (spatialFinite π n) :=
  NonUnitalStarAlgHom.isometry _ (spatialFinite_injective π hπ n)

omit [PartialOrder A] [StarOrderedRing A] in
lemma spatialFinite_successor (n : ℕ) (M : FinMatrix A n) :
    spatialFinite π (n+1) (matrixSuccessor n M) = spatialFinite π n M := by
  change (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), spatialEntry π i.val j.val
      (Fin.lastCases (0 : A) (fun i => Fin.lastCases (0 : A) (M i) j) i)) =
    ∑ i : Fin n, ∑ j : Fin n, spatialEntry π i.val j.val (M i j)
  simp [Fin.sum_univ_castSucc]

theorem spatialFinite_compatible {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n) :
    spatialFinite π m (matrixInclusion h M) = spatialFinite π n M := by
  change spatialFinite π m (matrixPad h M) = _
  induction m,h using Nat.le_induction with
  | base => rw [matrixPad_self]
  | succ m h ih => rw [matrixPad_succ h, spatialFinite_successor, ih]
end UnitalTomsWinter
end

noncomputable section

attribute [local instance 2000] UnitalTomsWinter.stabilizationHilbertNormedAddCommGroup
  UnitalTomsWinter.stabilizationHilbertSeminormedAddCommGroup
  UnitalTomsWinter.stabilizationHilbertAddCommMonoid
  UnitalTomsWinter.stabilizationHilbertContinuousAdd
  UnitalTomsWinter.stabilizationHilbertModule
  UnitalTomsWinter.stabilizationHilbertInnerProductSpace
  UnitalTomsWinter.stabilizationHilbertNormedSpace

local instance (priority := 2000) directFastUnitalTomsWinterSpatialCompletionRing (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Ring (UnitalTomsWinter.StabilizationOperators H) := ContinuousLinearMap.ring
local instance (priority := 2000) directFastUnitalTomsWinterSpatialCompletionCStar (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    CStarAlgebra (UnitalTomsWinter.StabilizationOperators H) := instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace
local instance (priority := 2000) directFastUnitalTomsWinterSpatialCompletionSemiring (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Semiring (UnitalTomsWinter.StabilizationOperators H) := (directFastUnitalTomsWinterSpatialCompletionRing H).toSemiring
local instance (priority := 2000) directFastUnitalTomsWinterSpatialCompletionNonSemiring (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    NonUnitalSemiring (UnitalTomsWinter.StabilizationOperators H) := (directFastUnitalTomsWinterSpatialCompletionRing H).toNonUnitalSemiring
local instance (priority := 2000) directFastUnitalTomsWinterSpatialCompletionNonAssoc (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    NonUnitalNonAssocSemiring (UnitalTomsWinter.StabilizationOperators H) :=
  (directFastUnitalTomsWinterSpatialCompletionRing H).toNonUnitalNonAssocSemiring
local instance (priority := 2000) directFastUnitalTomsWinterSpatialCompletionAdd (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    AddMonoid (UnitalTomsWinter.StabilizationOperators H) := ContinuousLinearMap.instAddMonoid

open scoped CStarAlgebra Topology

namespace UnitalTomsWinter
open TraceCone

variable {A H : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))

instance stabilizationOperatorsCStar : CStarAlgebra (StabilizationOperators H) :=
  directFastUnitalTomsWinterSpatialCompletionCStar H
instance stabilizationOperatorsContinuousStar : ContinuousStar (StabilizationOperators H) :=
  inferInstanceAs (ContinuousStar (SpatialHilbert H StandardHilbert →L[ℂ] SpatialHilbert H StandardHilbert))
instance stabilizationOperatorsTopologicalRing : IsTopologicalRing (StabilizationOperators H) :=
  inferInstanceAs (IsTopologicalRing (SpatialHilbert H StandardHilbert →L[ℂ] SpatialHilbert H StandardHilbert))

def spatialRepresentation : MatrixLimit A →⋆ₙₐ[ℂ] StabilizationOperators H :=
  matrixLimitLift (A := A) (B := StabilizationOperators H) (spatialFinite π) (spatialFinite_compatible π)

@[simp] theorem spatialRepresentation_stage (n : ℕ) (M : FinMatrix A n) :
    spatialRepresentation π (matrixLimitStage n M) = spatialFinite π n M :=
  matrixLimitLift_stage _ _ n M

lemma spatialRepresentation_continuous : Continuous (spatialRepresentation π) := by
  have h : LipschitzWith 1 (spatialRepresentation π) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul] using
      NonUnitalStarAlgHom.norm_apply_le (spatialRepresentation π) (x-y)
  exact h.continuous

theorem spatialRepresentation_norm (hπ : Function.Injective π) (x : MatrixLimit A) :
    ‖spatialRepresentation π x‖ = ‖x‖ := by
  refine finiteMatrixSubalgebra_dense.induction_on x ?_ ?_
  · have hc : Continuous (fun x : MatrixLimit A => ‖spatialRepresentation π x‖) :=
      continuous_norm.comp (spatialRepresentation_continuous π)
    exact isClosed_eq hc continuous_norm
  · intro y
    obtain ⟨n,M,rfl⟩ := finiteMatrixStage_surjective y
    change ‖spatialRepresentation π (matrixLimitStage n M)‖ = ‖matrixLimitStage n M‖
    rw [spatialRepresentation_stage, matrixLimitStage_norm]
    exact NonUnitalStarAlgHom.norm_map _ (spatialFinite_injective π hπ n) M

theorem spatialRepresentation_isometry (hπ : Function.Injective π) :
    Isometry (spatialRepresentation π) :=
  AddMonoidHomClass.isometry_of_norm (spatialRepresentation π) (spatialRepresentation_norm π hπ)

def spatialMatrixAlgebra : NonUnitalStarSubalgebra ℂ (StabilizationOperators H) :=
  (NonUnitalStarAlgebra.adjoin ℂ {T | ∃ (n : ℕ) (M : FinMatrix A n), T = spatialFinite π n M}).topologicalClosure

lemma spatialRepresentation_mem (x : MatrixLimit A) :
    spatialRepresentation π x ∈ spatialMatrixAlgebra π := by
  refine finiteMatrixSubalgebra_dense.induction_on x ?_ ?_
  · exact (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).preimage
      (spatialRepresentation_continuous π)
  · intro y
    obtain ⟨n,M,rfl⟩ := finiteMatrixStage_surjective y
    change spatialRepresentation π (matrixLimitStage n M) ∈ _
    rw [spatialRepresentation_stage]
    exact NonUnitalStarSubalgebra.le_topologicalClosure _
      (NonUnitalStarAlgebra.subset_adjoin ℂ _ ⟨n,M,rfl⟩)

theorem spatialRepresentation_range (hπ : Function.Injective π) :
    Set.range (spatialRepresentation π) = (spatialMatrixAlgebra π : Set (StabilizationOperators H)) := by
  apply Set.Subset.antisymm
  · rintro T ⟨x,rfl⟩; exact spatialRepresentation_mem π x
  · have hr : IsClosed (Set.range (spatialRepresentation π)) :=
      (spatialRepresentation_isometry π hπ).isClosedEmbedding.isClosed_range
    apply closure_minimal ?_ hr
    intro T hT
    induction hT using NonUnitalStarAlgebra.adjoin_induction with
    | mem T hT =>
      obtain ⟨n,M,rfl⟩ := hT
      exact ⟨matrixLimitStage n M, spatialRepresentation_stage π n M⟩
    | zero => exact ⟨0,map_zero _⟩
    | add T S _ _ hT hS =>
      obtain ⟨x,rfl⟩ := hT; obtain ⟨y,rfl⟩ := hS
      exact ⟨x+y,map_add _ _ _⟩
    | mul T S _ _ hT hS =>
      obtain ⟨x,rfl⟩ := hT; obtain ⟨y,rfl⟩ := hS
      exact ⟨x*y,map_mul _ _ _⟩
    | smul c T _ hT =>
      obtain ⟨x,rfl⟩ := hT; exact ⟨c • x,map_smul _ _ _⟩
    | star T _ hT =>
      obtain ⟨x,rfl⟩ := hT; exact ⟨star x,map_star _ _⟩
end UnitalTomsWinter
end

end OAI
