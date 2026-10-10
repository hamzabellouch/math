import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder

namespace Kadison.MatrixDiagonal

open Matrix

variable {A I : Type*} [CStarAlgebra A] [Fintype I] [DecidableEq I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (o : I)

def diagonal : A →ₗ[ℂ] A :=
  ∑ i,(LinearMap.mulLeft ℂ (φ (single i o 1))).comp (LinearMap.mulRight ℂ (φ (single o i 1)))

lemma diagonal_apply (a : A) : diagonal φ o a=∑ i,φ (single i o 1)*a*φ (single o i 1) := by
  simp only [diagonal,LinearMap.sum_apply,LinearMap.comp_apply,
    LinearMap.mulLeft_apply,LinearMap.mulRight_apply,mul_assoc]

lemma single_left (a : A) (k l : I) :
    φ (single k l 1)*diagonal φ o a=φ (single k o 1)*a*φ (single o l 1) := by
  rw [diagonal_apply,Finset.mul_sum,Finset.sum_eq_single l]
  · rw [←mul_assoc,←mul_assoc,←map_mul,single_mul_single_same,one_mul]
  · intro i hi hil
    rw [←mul_assoc,←mul_assoc,←map_mul,single_mul_single_of_ne 1 k l i hil.symm 1,
      map_zero,zero_mul,zero_mul]
  · simp

lemma single_right (a : A) (k l : I) :
    diagonal φ o a*φ (single k l 1)=φ (single k o 1)*a*φ (single o l 1) := by
  rw [diagonal_apply,Finset.sum_mul,Finset.sum_eq_single k]
  · rw [mul_assoc,mul_assoc,←map_mul,single_mul_single_same,one_mul,mul_assoc]
  · intro i hi hik
    rw [mul_assoc,mul_assoc,←map_mul,single_mul_single_of_ne 1 o i k hik 1,
      map_zero,mul_zero,mul_zero]
  · simp

lemma commutes (a : A) (x : Matrix I I ℂ) :
    φ x*diagonal φ o a=diagonal φ o a*φ x := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single x]
  conv_rhs => rw [Matrix.matrix_eq_sum_single x]
  simp only [map_sum,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  have hs : single k l (x k l)=(x k l) • single k l (1:ℂ) := by simp
  rw [hs,map_smul,smul_mul_assoc,mul_smul_comm,single_left,single_right]

lemma cut (a : A) :
    φ (single o o 1)*diagonal φ o a*φ (single o o 1)=
      φ (single o o 1)*a*φ (single o o 1) := by
  rw [single_left,mul_assoc,←map_mul,single_mul_single_same,one_mul]

lemma star_diagonal (a : A) : star (diagonal φ o a)=diagonal φ o (star a) := by
  simp only [diagonal_apply,star_sum,star_mul,←map_star,Matrix.star_eq_conjTranspose,
    conjTranspose_single,star_one,mul_assoc]

lemma mul_diagonal (a b : A) (ha : a*φ (single o o 1)=a) :
    diagonal φ o a*diagonal φ o b=diagonal φ o (a*b) := by
  conv_lhs => lhs; rw [diagonal_apply]
  rw [Finset.sum_mul]
  conv_rhs => rw [diagonal_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc,single_left]
  simp only [mul_assoc]
  rw [←mul_assoc a,ha]

lemma projection {p : A} (hp : IsStarProjection p) (hpr : p*φ (single o o 1)=p) :
    IsStarProjection (diagonal φ o p) := by
  constructor
  · change diagonal φ o p*diagonal φ o p=diagonal φ o p
    rw [mul_diagonal φ o p p hpr,hp.isIdempotentElem.eq]
  · change star (diagonal φ o p)=diagonal φ o p
    rw [star_diagonal,hp.isSelfAdjoint.star_eq]

lemma at_unit : diagonal φ o (φ (single o o 1))=1 := by
  rw [diagonal_apply]
  simp only [←map_mul,single_mul_single_same,one_mul,←map_sum,sum_single_one,map_one]

lemma fixed (a : A) (ha : ∀ x : Matrix I I ℂ,φ x*a=a*φ x) :
    diagonal φ o (φ (single o o 1)*a*φ (single o o 1))=a := by
  rw [diagonal_apply]
  have hpoint (i : I) :
      φ (single i o 1)*(φ (single o o 1)*a*φ (single o o 1))*φ (single o i 1)=
        φ (single i i 1)*a := by
    calc
      _=(φ (single i o 1)*φ (single o o 1))*a*(φ (single o o 1)*φ (single o i 1)) := by simp only [mul_assoc]
      _=φ (single i o 1)*a*φ (single o i 1) := by simp only [←map_mul,single_mul_single_same,one_mul]
      _=a*φ (single i i 1) := by rw [ha,mul_assoc,←map_mul,single_mul_single_same,one_mul]
      _=φ (single i i 1)*a := (ha _).symm
  simp only [hpoint,←Finset.sum_mul,←map_sum,sum_single_one,map_one,one_mul]

lemma matrix_block (a : A) (i j : I) :
    φ (single i o 1)*(φ (single o o 1)*(φ (single o i 1)*a*φ (single j o 1))*
      φ (single o o 1))*φ (single o j 1)=φ (single i i 1)*a*φ (single j j 1) := by
  calc
    _=(φ (single i o 1)*φ (single o o 1)*φ (single o i 1))*a*
        (φ (single j o 1)*φ (single o o 1)*φ (single o j 1)) := by simp only [mul_assoc]
    _=_ := by simp only [←map_mul,single_mul_single_same,one_mul]

lemma central_of_commutes_diagonal (c : A)
    (hc : ∀ x : Matrix I I ℂ,Commute (φ x) c)
    (hd : ∀ a : A,Commute (diagonal φ o a) c) (a : A) : Commute a c := by
  have hcorner (b : A) : Commute (φ (single o o 1)*b*φ (single o o 1)) c := by
    have he := ((hc (single o o 1)).mul_left (hd b)).mul_left (hc (single o o 1))
    rwa [cut] at he
  have hblock (i j : I) : Commute (φ (single i i 1)*a*φ (single j j 1)) c := by
    have he := ((hc (single i o 1)).mul_left
      (hcorner (φ (single o i 1)*a*φ (single j o 1)))).mul_left (hc (single o j 1))
    rwa [matrix_block] at he
  have hs := Commute.sum_left Finset.univ
    (fun i => ∑ j,φ (single i i 1)*a*φ (single j j 1)) c
    (fun i _ => Commute.sum_left Finset.univ _ c (fun j _ => hblock i j))
  simpa only [←Finset.mul_sum,←Finset.sum_mul,←map_sum,sum_single_one,map_one,
    mul_one,one_mul] using hs

end Kadison.MatrixDiagonal

end

end
end

end OAI
