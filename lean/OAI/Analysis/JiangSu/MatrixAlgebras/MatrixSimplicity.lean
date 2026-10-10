import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.MatrixAlgebras.CornerCompression
import OAI.Analysis.JiangSu.TraceCone.Pullback

namespace OAI


noncomputable section
open scoped CStarAlgebra

namespace Pureness
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [PartialOrder A] [StarOrderedRing A] in
lemma singleMatrix_sandwich (i j k l : ι) (M : CStarMatrix ι ι A) :
    singleMatrix i j 1 * M * singleMatrix k l 1 = singleMatrix i l (M j k) := by
  change CStarMatrix.ofMatrixStarAlgEquiv (Matrix.single i j 1) *
    CStarMatrix.ofMatrixStarAlgEquiv (CStarMatrix.ofMatrix.symm M) *
    CStarMatrix.ofMatrixStarAlgEquiv (Matrix.single k l 1) = _
  rw [← map_mul, ← map_mul, Matrix.single_mul_mul_single]
  simp only [one_mul, mul_one]
  rfl

lemma matrixCorner_eq_single {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (a : A) :
    TraceCone.matrixCorner i a = singleMatrix i i a := rfl

def matrixCornerIdeal (I : TwoSidedIdeal (CStarMatrix ι ι A)) (i : ι) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' {a | TraceCone.matrixCorner i a ∈ I}
    (by simp only [Set.mem_ofPred_eq, map_zero]; exact I.zero_mem)
    (by intro a b ha hb; simpa only [Set.mem_ofPred_eq, map_add] using I.add_mem ha hb)
    (by intro a ha; simpa only [Set.mem_ofPred_eq, map_neg] using I.neg_mem ha)
    (by intro a b hb; simpa only [Set.mem_ofPred_eq, map_mul] using I.mul_mem_left (TraceCone.matrixCorner i a) _ hb)
    (by intro a b ha; simpa only [Set.mem_ofPred_eq, map_mul] using I.mul_mem_right _ (TraceCone.matrixCorner i b) ha)

lemma matrixCornerIdeal_closed (I : TwoSidedIdeal (CStarMatrix ι ι A))
    (hI : IsClosed (I : Set (CStarMatrix ι ι A))) (i : ι) :
    IsClosed (matrixCornerIdeal I i : Set A) :=
  by
    have hc : Continuous (TraceCone.matrixCorner (A := A) i) :=
      (NonUnitalStarAlgHom.isometry _ (by
        intro a b h
        simpa [TraceCone.matrixCorner] using congrArg (fun M : CStarMatrix ι ι A => M i i) h)).continuous
    simpa only [matrixCornerIdeal, TwoSidedIdeal.coe_mk', Set.preimage, SetLike.mem_coe] using hI.preimage hc

theorem matrix_topologicallySimple [Nonempty ι] (hsimple : TopologicallySimple A) :
    TopologicallySimple (CStarMatrix ι ι A) := by
  intro I hI
  let i : ι := Classical.choice inferInstance
  rcases hsimple (matrixCornerIdeal I i) (matrixCornerIdeal_closed I hI i) with hz | ht
  · left
    apply le_antisymm ?_ bot_le
    intro M hM
    have he (j k : ι) : M j k = 0 := by
      have hm := I.mul_mem_right _ (singleMatrix k i 1)
        (I.mul_mem_left (singleMatrix i j 1) M hM)
      rw [singleMatrix_sandwich] at hm
      have hc : M j k ∈ matrixCornerIdeal I i := by
        simpa only [matrixCornerIdeal, TwoSidedIdeal.mem_mk', Set.mem_ofPred_eq, matrixCorner_eq_single] using hm
      rw [hz] at hc
      simpa using hc
    have hm : M = 0 := by ext j k; exact he j k
    simp [hm]
  · right
    apply top_unique
    intro M _
    have hi : singleMatrix i i (1 : A) ∈ I := by
      have h : (1 : A) ∈ matrixCornerIdeal I i := by rw [ht]; trivial
      simpa only [matrixCornerIdeal, TwoSidedIdeal.mem_mk', Set.mem_ofPred_eq, matrixCorner_eq_single] using h
    have hs (j k : ι) (a : A) : singleMatrix j k a ∈ I := by
      have h := I.mul_mem_right _ (singleMatrix i k 1)
        (I.mul_mem_left (singleMatrix j i a) _ hi)
      simpa only [singleMatrix_mul_same, mul_one] using h
    rw [matrix_eq_sum_single M]
    exact sum_mem fun j _ => sum_mem fun k _ => hs j k (M j k)

end Pureness
end

end OAI
