import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder Matrix

namespace Kadison.MatrixCorners

variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] Classical.propDecidable

omit [DecidableEq I] in
lemma projection_hermitian (p : Matrix I I ℂ) (hp : IsStarProjection p) : p.IsHermitian := hp.isSelfAdjoint

def projectionIndices (p : Matrix I I ℂ) (hp : IsStarProjection p) : Set I :=
  {i | (projection_hermitian p hp).eigenvalues i = 1}

lemma projection_eigenvalue (p : Matrix I I ℂ) (hp : IsStarProjection p) (i : I) :
    (projection_hermitian p hp).eigenvalues i=0 ∨ (projection_hermitian p hp).eigenvalues i=1 := by
  let U := (projection_hermitian p hp).eigenvectorUnitary
  have hid := congrArg (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) (star U)) hp.isIdempotentElem.eq
  rw [map_mul] at hid
  have hd := (projection_hermitian p hp).conjStarAlgAut_star_eigenvectorUnitary
  change Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) (star U) p = _ at hd
  rw [hd] at hid
  have h := congrArg (fun M : Matrix I I ℂ => (M i i).re) hid
  simp only [Matrix.diagonal_mul_diagonal,Matrix.diagonal_apply_eq,Function.comp_apply,
    ] at h
  change ((projection_hermitian p hp).eigenvalues i : ℂ).re *
    ((projection_hermitian p hp).eigenvalues i : ℂ).re -
    ((projection_hermitian p hp).eigenvalues i : ℂ).im *
    ((projection_hermitian p hp).eigenvalues i : ℂ).im =
    ((projection_hermitian p hp).eigenvalues i : ℂ).re at h
  simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] at h
  have hz : (projection_hermitian p hp).eigenvalues i *
      ((projection_hermitian p hp).eigenvalues i-1)=0 := by nlinarith
  exact (mul_eq_zero.mp hz).imp id sub_eq_zero.mp

lemma projection_diagonal_form (p : Matrix I I ℂ) (hp : IsStarProjection p) :
    p=Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) (projection_hermitian p hp).eigenvectorUnitary
      (Matrix.diagonal (fun i => if i∈projectionIndices p hp then (1:ℂ) else 0)) := by
  apply (projection_hermitian p hp).spectral_theorem.trans
  congr 1
  ext i j
  by_cases h : i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq,Function.comp_apply,projectionIndices,Set.mem_ofPred_eq]
    rcases projection_eigenvalue p hp i with he|he <;> simp [he]
  · simp [Matrix.diagonal_apply_ne _ h]

lemma trace_conjugation (U : unitary (Matrix I I ℂ)) (a : Matrix I I ℂ) :
    (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) U a).trace=a.trace := by
  rw [Unitary.conjStarAlgAut_apply,Matrix.trace_mul_comm,←mul_assoc,Unitary.coe_star_mul_self,one_mul]

lemma projection_trace (p : Matrix I I ℂ) (hp : IsStarProjection p) :
    p.trace=(Fintype.card (projectionIndices p hp):ℂ) := by
  classical
  calc
    _ = _ := congrArg Matrix.trace (projection_diagonal_form p hp)
    _ = _ := by
      rw [trace_conjugation,Matrix.trace_diagonal]
      simp [Fintype.card_subtype]

end Kadison.MatrixCorners

end

end
end

end OAI
