import OAI.Analysis.Nuclearity.CPNormFromPositive

namespace OAI

/-! Finite matrix amplification of completely positive contractions. Only
finite reindexing and the positive matrix norm bound are used. -/

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {A B m n : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [Fintype m] [Fintype n]

omit [Fintype n] in
lemma sum_cstarMatrix_apply {ι : Type*} [Fintype ι]
    (S : ι → CStarMatrix n n A) (i j : n) :
    (∑ k, S k) i j = ∑ k, S k i j :=
  map_sum (matrixEntryLinear i j) S Finset.univ

def flattenCStarMatrix : CStarMatrix m m (CStarMatrix n n A) →⋆ₙₐ[ℂ]
    CStarMatrix (m × n) (m × n) A where
  toFun M := fun i j => M i.1 j.1 i.2 j.2
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' M N := by
    ext i j
    change (M * N) i.1 j.1 i.2 j.2 =
      ∑ k : m × n, M i.1 k.1 i.2 k.2 * N k.1 j.1 k.2 j.2
    simp only [CStarMatrix.mul_apply, sum_cstarMatrix_apply, Fintype.sum_prod_type]
  map_star' M := by
    ext i j
    rfl

def unflattenCStarMatrix : CStarMatrix (m × n) (m × n) A →⋆ₙₐ[ℂ]
    CStarMatrix m m (CStarMatrix n n A) where
  toFun M := fun i j k l => M (i, k) (j, l)
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' M N := by
    ext i j k l
    change (M * N) (i, k) (j, l) =
      (∑ p : m, (CStarMatrix.ofMatrix (fun a b => M (i, a) (p, b))) *
        (CStarMatrix.ofMatrix (fun a b => N (p, a) (j, b)))) k l
    simp only [CStarMatrix.mul_apply, sum_cstarMatrix_apply, Fintype.sum_prod_type]
    rfl
  map_star' M := by
    ext i j k l
    rfl

lemma unflatten_flattenCStarMatrix (M : CStarMatrix m m (CStarMatrix n n A)) :
    unflattenCStarMatrix (flattenCStarMatrix M) = M := rfl

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

local instance amplifiedOrder : PartialOrder (CStarMatrix n n A) := CStarAlgebra.spectralOrder _
local instance amplifiedOrdered : StarOrderedRing (CStarMatrix n n A) := CStarAlgebra.spectralOrderedRing _
local instance amplifiedBOrder : PartialOrder (CStarMatrix n n B) := CStarAlgebra.spectralOrder _
local instance amplifiedBOrdered : StarOrderedRing (CStarMatrix n n B) := CStarAlgebra.spectralOrderedRing _

lemma matrixLinearMap_completelyPositive (φ : A →L[ℂ] B) (hφ : CompletelyPositive φ) :
    CompletelyPositive (matrixLinearMap (n := n) φ) := by
  intro k M hM
  have hflat := map_nonneg (flattenCStarMatrix (m := Fin k) (n := n)) hM
  have hmap := matrixLinearMap_nonneg hφ hflat
  have h := map_nonneg (unflattenCStarMatrix (m := Fin k) (n := n)) hmap
  exact h

section UnitalTarget

variable {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

local instance amplifiedDOrder : PartialOrder (CStarMatrix n n D) := CStarAlgebra.spectralOrder _
local instance amplifiedDOrdered : StarOrderedRing (CStarMatrix n n D) := CStarAlgebra.spectralOrderedRing _

lemma matrixLinearMap_norm_le_one (φ : A →L[ℂ] D) (hφ : CompletelyPositive φ) (hφn : ‖φ‖ ≤ 1) :
    ‖matrixLinearMap (n := n) φ‖ ≤ 1 := by
  classical
  apply cp_norm_le_one_of_positive_bound_nonunital _ (matrixLinearMap_completelyPositive φ hφ)
  intro M hM
  exact (norm_matrixLinearMap_nonneg_le hφ M hM).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hφn (norm_nonneg M))

end UnitalTarget
end WeakPureInfiniteness

end

end OAI
