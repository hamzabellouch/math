import Mathlib
import OAI.Analysis.FreeWords.MatrixAverageBasic

namespace OAI

noncomputable section

namespace KKMatrixQuantization

noncomputable section

variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

def matrixReindex (e : ι ≃ κ) : Matrix ι ι ℂ →⋆ₐ[ℂ] Matrix κ κ ℂ where
  __ := (Matrix.reindexAlgEquiv ℂ ℂ e).toAlgHom
  map_star' x := by ext i j; rfl

@[simp] theorem matrixReindex_single (e : ι ≃ κ) (i j : ι) (c : ℂ) :
    matrixReindex e (Matrix.single i j c)=Matrix.single (e i) (e j) c := by
  ext k l
  change Matrix.single i j c (e.symm k) (e.symm l)=Matrix.single (e i) (e j) c k l
  simp only [Matrix.single_apply,Equiv.eq_symm_apply]

omit [StarModule ℂ A] in
theorem reindex_average (e : ι ≃ κ) (ρ : Matrix ι ι ℂ →⋆ₐ[ℂ] A) (x : A) :
    matrixAverage (ρ.comp (matrixReindex e.symm)) x=matrixAverage ρ x := by
  simp only [matrixAverage,StarAlgHom.comp_apply,matrixReindex_single]
  rw [Fintype.card_congr e.symm]
  congr 1
  exact Fintype.sum_equiv e.symm _ _ (fun i => by
    exact Fintype.sum_equiv e.symm _ _ (fun j => rfl))

end

end KKMatrixQuantization
end

end OAI
