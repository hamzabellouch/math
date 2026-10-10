import OAI.Analysis.FreeEntropy.MatrixPolynomialNorm

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace FiniteEntropySeparation
 def matrixCoordinatesOfHermitian {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ) : MatrixCoordinates n d :=
  WithLp.toLp 2 (fun (i,j,k) => if j=k then (A i j j).re else if j<k then Real.sqrt 2*(A i j k).re else Real.sqrt 2*(A i k j).im)
 theorem hermitianMatrix_coordinatesOfHermitian {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i,(A i).IsHermitian) (i : Fin n) :
    hermitianMatrix (matrixCoordinatesOfHermitian A) i = A i := by
  have hs : (Real.sqrt 2:ℂ)≠0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)))
  ext j k
  have he := congrFun (congrFun (hA i) j) k
  change conj (A i k j)=A i j k at he
  by_cases hjk:j=k
  · subst k
    have hi := congrArg Complex.im he
    simp only [Complex.conj_im] at hi
    have heq : (A i j j).im=0 := by linarith
    simp only [hermitianMatrix,matrixCoordinatesOfHermitian,PiLp.toLp_apply,ite_true]
    exact Complex.ext (by simp) (by simp [heq])
  · have hkj := Ne.symm hjk
    rcases lt_or_gt_of_ne hjk with hlt | hgt
    · simp only [hermitianMatrix,matrixCoordinatesOfHermitian,PiLp.toLp_apply,hjk,hkj,hlt,not_lt_of_gt hlt,ite_false,ite_true,Complex.ofReal_mul]
      rw [div_eq_iff hs]
      apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring
    · simp only [hermitianMatrix,matrixCoordinatesOfHermitian,PiLp.toLp_apply,hjk,hkj,hgt,not_lt_of_gt hgt,ite_false,ite_true,Complex.ofReal_mul]
      rw [div_eq_iff hs,← he]
      apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring
end FiniteEntropySeparation

end

end OAI
