import OAI.Analysis.Pureness.Stabilization.MatrixMasks

namespace OAI
noncomputable section
open scoped CStarAlgebra
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def matrixRestrict {n m : ℕ} (h : n ≤ m) (M : FinMatrix A m) : FinMatrix A n :=
  CStarMatrix.ofMatrix (fun i j => M (Fin.castLE h i) (Fin.castLE h j))

omit [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma matrixRestrict_self (n : ℕ) (M : FinMatrix A n) : matrixRestrict le_rfl M = M := rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma matrixMask_eraseLast {n m : ℕ} (h : n ≤ m) (M : FinMatrix A (m+1)) :
    matrixMask n M = matrixSuccessor m (matrixMask n (matrixRestrict (Nat.le_succ m) M)) := by
  apply CStarMatrix.ext; intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j <;>
      simp [not_lt_of_ge h]
  · refine Fin.lastCases ?_ (fun j => ?_) j <;>
      simp [not_lt_of_ge h]
    rfl

omit [PartialOrder A] [StarOrderedRing A] in
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
end CuntzTrace

end

end OAI
