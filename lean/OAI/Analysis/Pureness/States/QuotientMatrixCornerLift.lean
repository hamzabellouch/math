import OAI.Analysis.Pureness.Cuntz.MatrixTraceCorrespondence

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped CStarAlgebra
variable {D E : Type*} [CStarAlgebra D] [CStarAlgebra E]
variable {ι : Type*}
variable (φ : D →⋆ₙₐ[ℂ] E) (w : ι → E)

def matrixCornerTerm (i j : ι) (a : D) : E := w i*φ a*star (w j)

lemma matrixCornerTerm_add (i j : ι) (a b : D) :
    matrixCornerTerm φ w i j (a+b)=matrixCornerTerm φ w i j a+matrixCornerTerm φ w i j b := by
  simp only [matrixCornerTerm,map_add,mul_add,add_mul]

lemma matrixCornerTerm_star (i j : ι) (a : D) :
    star (matrixCornerTerm φ w i j a)=matrixCornerTerm φ w j i (star a) := by
  simp only [matrixCornerTerm,star_mul,star_star,map_star,mul_assoc]

variable [DecidableEq ι]
variable (horth : ∀ i j, star (w i)*w j=if i=j then φ 1 else 0)

include horth in
lemma matrixCornerTerm_mul (i j k l : ι) (a b : D) :
    matrixCornerTerm φ w i j a*matrixCornerTerm φ w k l b=
      if j=k then matrixCornerTerm φ w i l (a*b) else 0 := by
  unfold matrixCornerTerm
  calc
    _ = w i*(φ a*(star (w j)*w k)*φ b)*star (w l) := by noncomm_ring
    _ = _ := by
      rw [horth]
      split_ifs with h
      · rw [← map_mul,← map_mul,mul_one,map_mul]
      · simp

variable [Fintype ι]

def matrixCornerLift : CStarMatrix ι ι D →⋆ₙₐ[ℂ] E where
  toFun M := ∑ i, ∑ j, matrixCornerTerm φ w i j (M i j)
  map_zero' := by simp [matrixCornerTerm,CStarMatrix.zero_apply]
  map_add' M N := by simp only [CStarMatrix.add_apply,matrixCornerTerm_add,Finset.sum_add_distrib]
  map_smul' c M := by
    simp only [CStarMatrix.smul_apply,matrixCornerTerm,map_smul,mul_smul_comm,smul_mul_assoc,Finset.smul_sum]
    rfl
  map_star' M := by
    simp only [star_sum,matrixCornerTerm_star,CStarMatrix.star_apply]
    exact Finset.sum_comm
  map_mul' M N := by
    simp only [Finset.sum_mul,Finset.mul_sum,matrixCornerTerm_mul φ w horth]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    simp only [CStarMatrix.mul_apply,matrixCornerTerm,map_sum,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm

lemma matrixCornerLift_single (i j : ι) (a : D) :
    matrixCornerLift φ w horth (CStarMatrix.ofMatrix (Matrix.single i j a))=
      matrixCornerTerm φ w i j a := by
  change (∑ k, ∑ l, matrixCornerTerm φ w k l ((Matrix.single i j a) k l))=_
  simp [Matrix.single,matrixCornerTerm,apply_ite,ite_mul,ite_and]

lemma matrixCornerLift_first (i : ι) (hi : w i=φ 1) (a : D) :
    matrixCornerLift φ w horth (CStarMatrix.ofMatrix (Matrix.single i i a))=φ a := by
  rw [matrixCornerLift_single]
  simp only [matrixCornerTerm,hi,← map_star,star_one,← map_mul,one_mul,mul_one]
end CuntzPureness

end

end OAI
