import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators

namespace Kadison.MatrixUnits

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A] [StarRing A]
  [Algebra ℂ A] [StarModule ℂ A]

def representation (e : ι → ι → A)
    (hmul : ∀ i j k l, e i j * e k l = if j=k then e i l else 0)
    (hstar : ∀ i j, star (e i j)=e j i)
    (hone : ∑ i,e i i=1) : Matrix ι ι ℂ →⋆ₐ[ℂ] A where
  toFun x := ∑ i,∑ j,x i j • e i j
  map_zero' := by simp
  map_one' := by simpa [Matrix.one_apply] using hone
  map_add' x y := by simp [add_smul,Finset.sum_add_distrib]
  map_mul' x y := by
    simp only [Matrix.mul_apply,Finset.sum_smul,Finset.sum_mul,Finset.mul_sum,
      smul_mul_smul_comm,hmul,smul_ite,smul_zero]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    conv_rhs =>
      rw [Finset.sum_comm]
      arg 2
      ext j
      rw [Finset.sum_comm]
    exact Finset.sum_comm
  commutes' c := by
    change (∑ i,∑ j,(algebraMap ℂ (Matrix ι ι ℂ) c) i j • e i j)=_
    simp [Matrix.algebraMap_matrix_apply,←Finset.smul_sum,hone,Algebra.algebraMap_eq_smul_one]
  map_star' x := by
    simp only [Matrix.star_apply,star_sum,star_smul,hstar]
    exact Finset.sum_comm

@[simp] lemma representation_apply (e : ι → ι → A) (hmul) (hstar) (hone)
    (x : Matrix ι ι ℂ) : representation e hmul hstar hone x=∑ i,∑ j,x i j • e i j := rfl

omit [Fintype ι] [Algebra ℂ A] [StarModule ℂ A] in
lemma partialIsometry_cross (q : A) (p v : ι → A)
    (hsource : ∀ i, star (v i)*v i=q)
    (htarget : ∀ i, p i*v i=v i)
    (hself : ∀ i, star (p i)=p i)
    (horth : ∀ i j, i≠j → p i*p j=0) (i j : ι) :
    star (v i)*v j=if i=j then q else 0 := by
  split_ifs with h
  · subst j
    exact hsource i
  · have hleft : star (v i)*p i=star (v i) := by
      simpa only [star_mul,hself] using congrArg star (htarget i)
    calc
      _=(star (v i)*p i)*(p j*v j) := by rw [hleft,htarget]
      _=star (v i)*(p i*p j)*v j := by noncomm_ring
      _=0 := by rw [horth i j h,mul_zero,zero_mul]

def ofPartialIsometries (q : A) (p v : ι → A)
    (hsource : ∀ i, star (v i)*v i=q)
    (hfinal : ∀ i, v i*star (v i)=p i)
    (hfix : ∀ i, v i*q=v i)
    (htarget : ∀ i, p i*v i=v i)
    (hself : ∀ i, star (p i)=p i)
    (horth : ∀ i j, i≠j → p i*p j=0)
    (hone : ∑ i,p i=1) : Matrix ι ι ℂ →⋆ₐ[ℂ] A :=
  representation (fun i j => v i*star (v j)) (by
    intro i j k l
    calc
      _=v i*(star (v j)*v k)*star (v l) := by noncomm_ring
      _=if j=k then v i*star (v l) else 0 := by
        rw [partialIsometry_cross q p v hsource htarget hself horth]
        split_ifs
        · rw [hfix]
        · rw [mul_zero,zero_mul])
    (by intro i j; simp only [star_mul,star_star])
    (by simpa only [hfinal] using hone)

@[simp] lemma ofPartialIsometries_single (q : A) (p v : ι → A)
    (hsource) (hfinal) (hfix) (htarget) (hself) (horth) (hone)
    (i j : ι) :
    ofPartialIsometries q p v hsource hfinal hfix htarget hself horth hone
      (Matrix.single i j (1:ℂ))=v i*star (v j) := by
  classical
  simp [ofPartialIsometries,representation,Matrix.single_apply,ite_and]

end Kadison.MatrixUnits

end

end
end

end OAI
