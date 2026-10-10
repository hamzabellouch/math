import Mathlib

namespace OAI

noncomputable section

namespace KKMatrixBounds

noncomputable section

open scoped Matrix.Norms.Operator

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem unitary_entry_norm_le_one {n:ℕ} (U:unitary (Matrix (Fin n) (Fin n) A)) (i j:Fin n) :
    ‖U.val i j‖≤1 := by
  have hcol : ∑k:Fin n,star (U.val k j)*U.val k j=1 := by
    have h := congrArg (fun X : Matrix (Fin n) (Fin n) A => X j j) (Unitary.coe_star_mul_self U)
    simpa only [Matrix.mul_apply,Matrix.star_apply,Matrix.one_apply_eq] using h
  have hle : star (U.val i j)*U.val i j≤1 := by
    rw [←hcol]
    exact Finset.single_le_sum (fun k _ => star_mul_self_nonneg (U.val k j)) (Finset.mem_univ i)
  have hnorm := (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg _)).2 hle
  rw [CStarRing.norm_star_mul_self] at hnorm
  nlinarith [norm_nonneg (U.val i j)]

theorem unitary_rowSum_norm_le {n:ℕ} (U:unitary (Matrix (Fin n) (Fin n) A)) :
    ‖U.val‖≤n := by
  rw [Matrix.linfty_opNorm_def]
  change (↑(Finset.univ.sup fun i => ∑j:Fin n,‖U.val i j‖₊):ℝ)≤((n:NNReal):ℝ)
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro i hi
  change (∑j:Fin n,‖U.val i j‖₊:NNReal)≤(n:NNReal)
  calc
    _ ≤ ∑j:Fin n,(1:NNReal) := Finset.sum_le_sum (fun j _ => show ‖U.val i j‖₊≤1 from unitary_entry_norm_le_one U i j)
    _ = _ := by simp

end

end KKMatrixBounds
end

end OAI
