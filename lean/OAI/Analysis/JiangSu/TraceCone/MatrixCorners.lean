import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI


noncomputable section
namespace TraceCone.MatrixCorners
open scoped CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma matrixSuccessor_apply_castSucc (n : ℕ) (M : FinMatrix A n) (i j : Fin n) :
    matrixSuccessor n M i.castSucc j.castSucc = M i j := by
  simp only [matrixSuccessor]
  change Fin.lastCases 0 (fun i => Fin.lastCases 0 (M i) j.castSucc) i.castSucc = M i j
  simp only [Fin.lastCases_castSucc]

omit [PartialOrder A] [StarOrderedRing A] in
lemma matrixSuccessor_injective (n : ℕ) : Function.Injective (matrixSuccessor (A := A) n) := by
  intro M N h
  ext i j
  simpa only [matrixSuccessor_apply_castSucc] using
    congrArg (fun matrix : FinMatrix A (n + 1) => matrix i.castSucc j.castSucc) h

lemma matrixSuccessor_isometry (n : ℕ) : Isometry (matrixSuccessor (A := A) n) :=
  NonUnitalStarAlgHom.isometry _ (matrixSuccessor_injective n)

@[simp] lemma matrixSuccessor_norm (n : ℕ) (M : FinMatrix A n) :
    ‖matrixSuccessor n M‖ = ‖M‖ :=
  NonUnitalStarAlgHom.norm_map _ (matrixSuccessor_injective n) M
end TraceCone.MatrixCorners
end


noncomputable section
namespace TraceCone.MatrixCorners
open scoped CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma matrixPad_self (n : ℕ) (M : FinMatrix A n) : matrixPad le_rfl M = M :=
  Nat.leRecOn_self M

omit [PartialOrder A] [StarOrderedRing A] in
lemma matrixPad_trans {n m k : ℕ} (h : n ≤ m) (g : m ≤ k) (M : FinMatrix A n) :
    matrixPad g (matrixPad h M) = matrixPad (h.trans g) M :=
  (Nat.leRecOn_trans h g M).symm

@[simp] lemma matrixInclusion_norm {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n) :
    ‖matrixInclusion h M‖ = ‖M‖ := by
  change ‖matrixPad h M‖ = ‖M‖
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m h ih => rw [matrixPad_succ h, matrixSuccessor_norm, ih]

lemma matrixInclusion_isometry {n m : ℕ} (h : n ≤ m) :
    Isometry (matrixInclusion (A := A) h) :=
  AddMonoidHomClass.isometry_of_norm _ (matrixInclusion_norm h)

@[simp] lemma matrixInclusion_trans {n m k : ℕ} (h : n ≤ m) (g : m ≤ k)
    (M : FinMatrix A n) :
    matrixInclusion g (matrixInclusion h M) = matrixInclusion (h.trans g) M :=
  matrixPad_trans h g M
end TraceCone.MatrixCorners
end

end OAI
