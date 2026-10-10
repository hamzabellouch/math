import Mathlib

namespace OAI

noncomputable section

namespace KKVariableUltra

noncomputable section

variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

theorem kronecker_one_expansion (a : Matrix ι ι ℂ) :
    Matrix.kronecker a (1 : Matrix κ κ ℂ)=∑ i,∑ j,∑ k, a i j • Matrix.single (i,k) (j,k) 1 := by
  apply Matrix.ext
  rintro ⟨i,k⟩ ⟨j,l⟩
  change a i j * (if k=l then 1 else 0) = _
  simp only [Matrix.sum_apply,Matrix.smul_apply,
    Matrix.single_apply,Prod.mk.injEq,ite_and,smul_eq_mul]
  simp

end

end KKVariableUltra
end

end OAI
