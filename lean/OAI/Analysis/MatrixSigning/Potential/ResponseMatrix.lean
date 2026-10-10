import Mathlib
import OAI.Analysis.MatrixSigning.Potential.RowSquareSum

namespace OAI

open Matrix

namespace CurrentKS.Covariance
noncomputable section
open Matrix WithLp
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

variable {n : ℕ}

lemma pair_norm_sq (v : E (2*n)) : ‖v‖^2 = ‖fstVec v‖^2+‖sndVec v‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]
  rw [sum_pair]
  rfl

def responseMatrix (B : Mat n) : Matrix (Fin n) (Fin (2*n)) ℝ :=
  fun i j => Sum.elim (fun k => (1 : Mat n) i k) (fun k => -B i k) ((pairIndex n).symm j)

lemma responseMatrix_apply (B : Mat n) (v : E (2*n)) :
    (responseMatrix B).toEuclideanLin v = responseLin B v := by
  ext i
  change (∑ j, responseMatrix B i j*v j) = _
  rw [sum_pair]
  simp only [responseMatrix,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr]
  change (∑ j, (1 : Mat n) i j*fstVec v j)+(∑ j, -B i j*sndVec v j) = _
  simp only [neg_mul,Finset.sum_neg_distrib]
  change ((1 : Mat n) *ᵥ fstVec v) i-(B *ᵥ sndVec v) i = _
  rw [Matrix.one_mulVec]
  rfl

lemma response_row_squares (B : Mat n) (i : Fin n) :
    (∑ j, responseMatrix B i j^2) = 1+∑ j, B i j^2 := by
  rw [sum_pair]
  simp only [responseMatrix,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,neg_sq]
  have he : (∑ j, (1 : Mat n) i j^2) = 1 := by simp [Matrix.one_apply]
  rw [he]

lemma hermitian_row_norm_bound (B : Mat n) (hB : B.IsHermitian) (i : Fin n) :
    (∑ j, B i j^2) ≤ ‖B‖^2 := by
  let e : E n := EuclideanSpace.single i 1
  have he : ‖e‖ = 1 := by simp [e]
  have hn := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B).le_opNorm e
  rw [Matrix.l2_opNorm_toEuclideanCLM,he,mul_one] at hn
  have hh : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B) e‖^2 = ∑ j, B i j^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro j _
    have hs : B j i = B i j := by simpa only [Matrix.conjTranspose_apply,star_trivial] using (congrFun (congrFun hB j) i).symm
    simp only [Matrix.ofLp_toEuclideanCLM,e,PiLp.single_apply,Matrix.mulVec, dotProduct]
    simp [hs,Real.norm_eq_abs,sq_abs]
  rw [← hh]
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

lemma response_moment_upper (B : Mat n) (hB : B.IsHermitian) {Γ : Mat (2*n)}
    (hΓ : Γ.PosSemidef) (hbound : ((4 : ℝ) • (1 : Mat (2*n))-Γ).PosSemidef) (i : Fin n) :
    (∑ j, (responseLin B (column (CFC.sqrt Γ) j) i)^2) ≤ 4*(1+‖B‖^2) := by
  have hh := response_row_bound (responseMatrix B) hΓ hbound i
  simp only [responseMatrix_apply,response_row_squares] at hh
  exact hh.trans (by nlinarith [hermitian_row_norm_bound B hB i])

lemma constraints_responses (A B : Mat n) (v : E (2*n)) (hv : constraintLin A B v = 0) :
    fstVec v-B.toEuclideanLin (sndVec v) = responseLin B v ∧
    sndVec v-A.toEuclideanLin (fstVec v) = -responseLin B v := by
  refine ⟨rfl,?_⟩
  have hh : responseLin B v-(A.toEuclideanLin (fstVec v)-sndVec v) = 0 := hv
  rw [sub_eq_zero] at hh
  rw [hh]
  abel

end
end CurrentKS.Covariance

end OAI
