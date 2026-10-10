import OAI.Analysis.Pureness.Stabilization.MatrixCorners

namespace OAI
noncomputable section
namespace CuntzTrace
open scoped CStarAlgebra
variable {A : Type*} [NonUnitalCStarAlgebra A]

def matrixPad {n m : ℕ} (h : n ≤ m) : FinMatrix A n → FinMatrix A m :=
  Nat.leRecOn h (fun {k} => matrixSuccessor k)

@[simp] lemma matrixPad_self (n : ℕ) (M : FinMatrix A n) : matrixPad le_rfl M = M :=
  Nat.leRecOn_self M
lemma matrixPad_succ {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n) :
    matrixPad (Nat.le.step h) M = matrixSuccessor m (matrixPad h M) :=
  Nat.leRecOn_succ h M
lemma matrixPad_trans {n m k : ℕ} (h : n ≤ m) (g : m ≤ k) (M : FinMatrix A n) :
    matrixPad g (matrixPad h M) = matrixPad (h.trans g) M :=
  (Nat.leRecOn_trans h g M).symm

def matrixInclusion {n m : ℕ} (h : n ≤ m) : FinMatrix A n →⋆ₙₐ[ℂ] FinMatrix A m where
  toFun := matrixPad h
  map_zero' := by
    induction m, h using Nat.le_induction with
    | base => simp
    | succ m h ih => rw [matrixPad_succ h, ih, map_zero]
  map_add' M N := by
    induction m, h using Nat.le_induction with
    | base => simp
    | succ m h ih => simp only [matrixPad_succ h, ih, map_add]
  map_mul' M N := by
    induction m, h using Nat.le_induction with
    | base => simp
    | succ m h ih => simp only [matrixPad_succ h, ih, map_mul]
  map_smul' c M := by
    induction m, h using Nat.le_induction with
    | base => simp
    | succ m h ih => simp only [matrixPad_succ h, ih, map_smul]
  map_star' M := by
    induction m, h using Nat.le_induction with
    | base => simp
    | succ m h ih => simp only [matrixPad_succ h, ih, map_star]

section

variable [PartialOrder A] [StarOrderedRing A]

@[simp] lemma matrixInclusion_norm {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n) :
    ‖matrixInclusion h M‖ = ‖M‖ := by
  change ‖matrixPad h M‖ = ‖M‖
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m h ih => rw [matrixPad_succ h, matrixSuccessor_norm, ih]

lemma matrixInclusion_isometry {n m : ℕ} (h : n ≤ m) :
    Isometry (matrixInclusion (A := A) h) :=
  AddMonoidHomClass.isometry_of_norm _ (matrixInclusion_norm h)

end

@[simp] lemma matrixInclusion_trans {n m k : ℕ} (h : n ≤ m) (g : m ≤ k)
    (M : FinMatrix A n) :
    matrixInclusion g (matrixInclusion h M) = matrixInclusion (h.trans g) M :=
  matrixPad_trans h g M
end CuntzTrace

end

end OAI
