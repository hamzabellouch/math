import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.MatrixCorners
import OAI.Analysis.JiangSu.TraceCone.MatrixFamilies
import OAI.Analysis.JiangSu.TraceCone.MatrixMasks

namespace OAI


noncomputable section
open scoped CStarAlgebra

namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def matrixRestrict {n m : ℕ} (h : n ≤ m) (M : FinMatrix A m) : FinMatrix A n :=
  CStarMatrix.ofMatrix (fun i j => M (Fin.castLE h i) (Fin.castLE h j))

@[simp] lemma matrixRestrict_self {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    (n : ℕ) (M : FinMatrix A n) : matrixRestrict le_rfl M = M := rfl

lemma matrixMask_eraseLast {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {n m : ℕ} (h : n ≤ m) (M : FinMatrix A (m+1)) :
    matrixMask n M = matrixSuccessor m (matrixMask n (matrixRestrict (Nat.le_succ m) M)) := by
  apply CStarMatrix.ext; intro i j
  simp only [matrixSuccessor, matrixMask, matrixRestrict]
  change (if i.val < n ∧ j.val < n then M i j else (0 : A)) =
    Fin.lastCases (0 : A) (fun i => Fin.lastCases (0 : A)
      (fun j => if i.val < n ∧ j.val < n then
        M (Fin.castLE (Nat.le_succ m) i) (Fin.castLE (Nat.le_succ m) j) else (0 : A)) j) i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j <;>
      simp [not_lt_of_ge h]
  · refine Fin.lastCases ?_ (fun j => ?_) j <;>
      simp [not_lt_of_ge h]
    rfl

theorem matrixInclusion_restrict {n m : ℕ} (h : n ≤ m) (M : FinMatrix A m) :
    matrixInclusion h (matrixRestrict h M) = matrixMask n M := by
  change matrixPad h (matrixRestrict h M) = matrixMask n M
  induction m, h using Nat.le_induction with
  | base => rw [matrixRestrict_self,matrixPad_self,matrixMask_eq_self le_rfl]
  | succ m h ih =>
    rw [matrixPad_succ h,matrixMask_eraseLast h]
    have hr : matrixRestrict (Nat.le.step h) M =
        matrixRestrict h (matrixRestrict (Nat.le_succ m) M) := rfl
    rw [hr,ih]

theorem matrixRestrict_norm_le {n m : ℕ} (h : n ≤ m) (M : FinMatrix A m) :
    ‖matrixRestrict h M‖ ≤ ‖M‖ := by
  rw [← matrixInclusion_norm h, matrixInclusion_restrict]
  exact matrixMask_norm_le n M
end TraceCone
end


noncomputable section
open scoped ENNReal Topology CStarAlgebra

namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma matrixMask_stage_range (n m : ℕ) (M : FinMatrix A m) :
    matrixStage m (matrixMask n M) ∈ Set.range (matrixStage (A := A) n) := by
  rcases le_total m n with h | h
  · refine ⟨matrixInclusion h M,?_⟩
    rw [matrixStage_compatible,matrixMask_eq_self h]
  · refine ⟨matrixRestrict h M,?_⟩
    rw [← matrixInclusion_restrict h M,matrixStage_compatible]

theorem matrixCompression_range (n : ℕ) (x : MatrixLimit A) :
    ∃ M : FinMatrix A n, matrixLimitStage n M = matrixCompression n x := by
  have hs : IsClosed (Set.range (matrixStage (A := A) n)) :=
    (matrixStage_isometry n).isClosedEmbedding.isClosed_range
  have hc : IsClosed ((matrixQuotientMask (A := A) n) ⁻¹' Set.range (matrixStage (A := A) n)) :=
    hs.preimage (matrixQuotientMaskCLM n).continuous
  have hsub : (matrixUnion A : Set (FamilyQuotient (FinMatrix A))) ⊆
      (matrixQuotientMask n) ⁻¹' Set.range (matrixStage (A := A) n) := by
    rintro y ⟨m,M,rfl⟩
    change matrixQuotientMask n (matrixStage m M) ∈ Set.range (matrixStage (A := A) n)
    rw [matrixQuotientMask_stage]
    exact matrixMask_stage_range n m M
  obtain ⟨matrix, matrix_eq⟩ := closure_minimal hsub hc x.2
  exact ⟨matrix, Subtype.ext matrix_eq⟩

def matrixCornerExtract (n : ℕ) (x : MatrixLimit A) : FinMatrix A n :=
  (matrixCompression_range n x).choose

@[simp] theorem matrixCornerExtract_spec (n : ℕ) (x : MatrixLimit A) :
    matrixLimitStage n (matrixCornerExtract n x) = matrixCompression n x :=
  (matrixCompression_range n x).choose_spec

theorem matrixCornerExtract_norm_le (n : ℕ) (x : MatrixLimit A) : ‖matrixCornerExtract n x‖ ≤ ‖x‖ := by
  rw [← matrixLimitStage_norm n, matrixCornerExtract_spec]
  exact matrixCompression_norm_le n x

def matrixCornerExtractLinear (n : ℕ) : MatrixLimit A →ₗ[ℂ] FinMatrix A n where
  toFun := matrixCornerExtract n
  map_add' x y := by
    apply (matrixLimitStage_isometry n).injective
    simp only [map_add,matrixCornerExtract_spec]
  map_smul' c x := by
    apply (matrixLimitStage_isometry n).injective
    simp only [map_smul,matrixCornerExtract_spec,RingHom.id_apply]
end TraceCone
end

end OAI
