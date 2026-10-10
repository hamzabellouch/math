import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.MatrixAlgebras.SharedMatrixBridge
import OAI.Analysis.JiangSu.TraceCone.MatrixBlockNorm
import OAI.Analysis.JiangSu.CuntzSemigroup.CuntzOrder
import OAI.Analysis.JiangSu.MatrixAlgebras.CompletedCornerRange

namespace OAI


noncomputable section
open scoped CStarAlgebra

namespace Pureness
open TraceCone

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def FiniteCuntzClass (x : CuntzClass (MatrixLimit A)) : Prop :=
  ∃ (n : ℕ) (M : Positive (FinMatrix A n)), x = CuntzClass.mk (Positive.map (matrixLimitStage n) M)

lemma finiteCuntzClass_zero : FiniteCuntzClass (0 : CuntzClass (MatrixLimit A)) := by
  let : AddMonoid (MatrixLimit A) :=
    (NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (matrixLimitAlgebra A)).toAddMonoid
  refine ⟨0,Positive.zero,?_⟩
  apply congrArg CuntzClass.mk
  apply Subtype.ext
  exact (matrixLimitStage (A := A) 0).map_zero'.symm

lemma finiteCuntzClass_add {x y : CuntzClass (MatrixLimit A)}
    (hx : FiniteCuntzClass x) (hy : FiniteCuntzClass y) : FiniteCuntzClass (x+y) := by
  obtain ⟨n,M,rfl⟩ := hx
  obtain ⟨m,N,rfl⟩ := hy
  let l := max n m
  let M' := Positive.map (matrixInclusion (le_max_left n m)) M
  let N' := Positive.map (matrixInclusion (le_max_right n m)) N
  have hM : Positive.map (matrixLimitStage n) M = Positive.map (matrixLimitStage l) M' :=
    Subtype.ext (matrixLimitStage_compatible (le_max_left n m) M.1).symm
  have hN : Positive.map (matrixLimitStage m) N = Positive.map (matrixLimitStage l) N' :=
    Subtype.ext (matrixLimitStage_compatible (le_max_right n m) N.1).symm
  refine ⟨l*2,Positive.map (matrixInterleave l) (positiveProduct M' N'),?_⟩
  rw [hM,hN]
  exact congrArg CuntzClass.mk (matrixBlockPositive_stage l M' N')

def finiteCuntzSubmonoid : AddSubmonoid (CuntzClass (MatrixLimit A)) where
  carrier := FiniteCuntzClass
  zero_mem' := finiteCuntzClass_zero
  add_mem' := finiteCuntzClass_add

theorem shared_finiteClass_order_iff (k : ℕ) (M N : Positive (FinMatrix A k)) :
    CuntzClass.mk (Positive.map (matrixLimitStage k) M) ≤
      CuntzClass.mk (Positive.map (matrixLimitStage k) N) ↔ CuntzSubequiv M.1 N.1 := by
  rw [CuntzClass.mk_le_mk, ← shared_cuntz_map_equiv sharedMatrixEquiv,
    ← cuntzSubequiv_iff_shared]
  change CuntzSubequiv (sharedMatrixEquiv (matrixLimitStage k M.1))
    (sharedMatrixEquiv (matrixLimitStage k N.1)) ↔ _
  rw [sharedMatrixEquiv_stage, sharedMatrixEquiv_stage,
    cuntzSubequiv_completedMatrixInclude_iff]

theorem finiteCuntz_almostUnperforated
    (hAU : ∀ (u v : CuntzClass (MatrixLimit A)) (k : ℕ), 1 ≤ k →
      (k+1) • u ≤ k • v → u ≤ v)
    (u v : finiteCuntzSubmonoid (A := A)) (k : ℕ) (hk : 1 ≤ k)
    (h : (k+1) • u ≤ k • v) : u ≤ v := by
  exact hAU u.1 v.1 k hk h

end Pureness
end

end OAI
