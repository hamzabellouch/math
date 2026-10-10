import OAI.Analysis.Pureness.Stabilization.MatrixSystem
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Tactic.Linarith

namespace OAI
noncomputable section
open scoped CStarAlgebra
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A]

def matrixMask (n : ℕ) {m : ℕ} (M : FinMatrix A m) : FinMatrix A m :=
  CStarMatrix.ofMatrix (fun i j => if i.val < n ∧ j.val < n then M i j else 0)

@[simp] lemma matrixMask_apply (n : ℕ) {m : ℕ} (M : FinMatrix A m) (i j : Fin m) :
    matrixMask n M i j = if i.val < n ∧ j.val < n then M i j else 0 := rfl

lemma matrixMask_eq_self {n m : ℕ} (h : m ≤ n) (M : FinMatrix A m) : matrixMask n M = M := by
  apply CStarMatrix.ext; intro i j
  simp [i.isLt.trans_le h, j.isLt.trans_le h]

@[simp] lemma matrixMask_zero (n m : ℕ) : matrixMask (A := A) n (0 : FinMatrix A m) = 0 := by
  apply CStarMatrix.ext; intro i j; simp
@[simp] lemma matrixMask_add (n : ℕ) {m : ℕ} (M N : FinMatrix A m) :
    matrixMask n (M+N) = matrixMask n M + matrixMask n N := by
  apply CStarMatrix.ext; intro i j; simp only [matrixMask_apply, CStarMatrix.add_apply]; split_ifs <;> simp
@[simp] lemma matrixMask_smul (n : ℕ) {m : ℕ} (c : ℂ) (M : FinMatrix A m) :
    matrixMask n (c • M) = c • matrixMask n M := by
  apply CStarMatrix.ext; intro i j; simp only [matrixMask_apply, CStarMatrix.smul_apply]; split_ifs <;> simp
@[simp] lemma matrixMask_sub (n : ℕ) {m : ℕ} (M N : FinMatrix A m) :
    matrixMask n (M-N) = matrixMask n M - matrixMask n N := by
  apply CStarMatrix.ext; intro i j; simp only [matrixMask_apply, CStarMatrix.sub_apply]; split_ifs <;> simp

def matrixUnitize (m : ℕ) : FinMatrix A m →⋆ₙₐ[ℂ] FinMatrix (Unitization ℂ A) m :=
  CStarMatrix.mapₙₐ (Unitization.inrNonUnitalStarAlgHom ℂ A)

lemma matrixUnitize_injective (m : ℕ) : Function.Injective (matrixUnitize (A := A) m) := by
  intro M N h
  apply CStarMatrix.ext; intro i j
  exact Unitization.inr_injective (congrArg (fun P : FinMatrix (Unitization ℂ A) m => P i j) h)

@[simp] lemma matrixUnitize_norm [PartialOrder A] [StarOrderedRing A]
    (m : ℕ) (M : FinMatrix A m) : ‖matrixUnitize m M‖ = ‖M‖ :=
  NonUnitalStarAlgHom.norm_map _ (matrixUnitize_injective m) M

def matrixMaskProjection (n m : ℕ) : FinMatrix (Unitization ℂ A) m :=
  CStarMatrix.ofMatrix (Matrix.diagonal (fun i => if i.val < n then 1 else 0))

lemma matrixMaskProjection_star (n m : ℕ) : star (matrixMaskProjection (A := A) n m) = matrixMaskProjection n m := by
  apply CStarMatrix.ext; intro i j
  simp [matrixMaskProjection, Matrix.diagonal, CStarMatrix.star_apply]
  split_ifs <;> simp_all
  omega

lemma matrixMaskProjection_mul (n m : ℕ) : matrixMaskProjection (A := A) n m * matrixMaskProjection n m = matrixMaskProjection n m := by
  apply CStarMatrix.ext
  intro i j
  let d : Fin m → Unitization ℂ A := fun i => if i.val < n then 1 else 0
  change (Matrix.diagonal d * Matrix.diagonal d) i j = Matrix.diagonal d i j
  rw [Matrix.diagonal_mul_diagonal]
  have hd : (fun i => d i * d i) = d := by
    funext i
    simp only [d]
    split_ifs <;> simp
  rw [hd]

lemma matrixMaskProjection_norm_le (n m : ℕ) : ‖matrixMaskProjection (A := A) n m‖ ≤ 1 := by
  have h := CStarRing.norm_star_mul_self (x := matrixMaskProjection (A := A) n m)
  rw [matrixMaskProjection_star, matrixMaskProjection_mul] at h
  nlinarith [norm_nonneg (matrixMaskProjection (A := A) n m)]

lemma matrixMask_unitize (n : ℕ) {m : ℕ} (M : FinMatrix A m) :
    matrixUnitize m (matrixMask n M) = matrixMaskProjection n m * matrixUnitize m M * matrixMaskProjection n m := by
  apply CStarMatrix.ext; intro i j
  let d : Fin m → Unitization ℂ A := fun i => if i.val < n then 1 else 0
  let N : Matrix (Fin m) (Fin m) (Unitization ℂ A) := fun i j => (M i j : Unitization ℂ A)
  change ((matrixMask n M) i j : Unitization ℂ A) = (Matrix.diagonal d * N * Matrix.diagonal d) i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [matrixMask_apply, d, N]
  split_ifs <;> simp_all

theorem matrixMask_norm_le [PartialOrder A] [StarOrderedRing A]
    (n : ℕ) {m : ℕ} (M : FinMatrix A m) : ‖matrixMask n M‖ ≤ ‖M‖ := by
  rw [← matrixUnitize_norm m (matrixMask n M), matrixMask_unitize]
  have hp := matrixMaskProjection_norm_le (A := A) n m
  calc
    _ ≤ ‖matrixMaskProjection (A := A) n m‖ * ‖matrixUnitize m M‖ * ‖matrixMaskProjection (A := A) n m‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ‖M‖ := by
      rw [matrixUnitize_norm]
      nlinarith [norm_nonneg (matrixMaskProjection (A := A) n m), norm_nonneg M,
        mul_le_mul_of_nonneg_right hp (norm_nonneg M)]

lemma matrixMask_successor (n m : ℕ) (M : FinMatrix A m) :
    matrixMask n (matrixSuccessor m M) = matrixSuccessor m (matrixMask n M) := by
  apply CStarMatrix.ext; intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

lemma matrixMask_inclusion (n : ℕ) {m k : ℕ} (h : m ≤ k) (M : FinMatrix A m) :
    matrixMask n (matrixInclusion h M) = matrixInclusion h (matrixMask n M) := by
  change matrixMask n (matrixPad h M) = matrixPad h (matrixMask n M)
  induction k, h using Nat.le_induction with
  | base => simp
  | succ k h ih => rw [matrixPad_succ h, matrixPad_succ h, matrixMask_successor, ih]
end CuntzTrace

end

end OAI
