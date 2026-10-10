import Mathlib

namespace OAI

/-! Matrix ideal arithmetic, conjugation errors and triple commutator congruences. -/

noncomputable section
open scoped BigOperators commutatorElement
open Matrix

namespace BoundaryOnly.Holonomy
open Matrix
open scoped BigOperators commutatorElement
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

lemma matrix_mul_mem {I J : Ideal R} {A B : Matrix ι ι R}
    (hA : A ∈ I.matrix ι) (hB : B ∈ J.matrix ι) :
    A * B ∈ (I * J).matrix ι := by
  intro i j
  apply Ideal.sum_mem
  intro k _
  exact Ideal.mul_mem_mul (hA i k) (hB k j)

lemma matrix_mul_right {I : Ideal R} {A : Matrix ι ι R}
    (hA : A ∈ I.matrix ι) (B : Matrix ι ι R) : A * B ∈ I.matrix ι := by
  intro i j
  apply Ideal.sum_mem
  intro k _
  exact I.mul_mem_right _ (hA i k)

abbrev mat (u : SpecialLinearGroup ι R) : Matrix ι ι R := u

@[simp] lemma mat_mul (u v : SpecialLinearGroup ι R) : mat (u*v) = mat u * mat v := rfl
@[simp] lemma mat_one : mat (1 : SpecialLinearGroup ι R) = 1 := rfl

lemma inv_deviation {I : Ideal R} {u : SpecialLinearGroup ι R}
    (hu : mat u - 1 ∈ I.matrix ι) : mat u⁻¹ - 1 ∈ I.matrix ι := by
  have heq : mat u⁻¹ - 1 = -(mat u⁻¹ * (mat u - 1)) := by
    simp only [mul_sub, ← mat_mul, inv_mul_cancel,
      mat_one, mul_one, neg_sub]
  rw [heq]
  exact (I.matrix ι).neg_mem ((I.matrix ι).mul_mem_left _ hu)

lemma product_deviation {I : Ideal R} {u v : SpecialLinearGroup ι R}
    (hu : mat u - 1 ∈ I.matrix ι) (hv : mat v - 1 ∈ I.matrix ι) :
    mat (u*v) - 1 ∈ I.matrix ι := by
  have heq : mat (u*v) - 1 = mat u * (mat v - 1) + (mat u - 1) := by
    simp only [mat_mul, mul_sub, mul_one]
    abel
  rw [heq]
  exact (I.matrix ι).add_mem ((I.matrix ι).mul_mem_left _ hv) hu

 

lemma commutator_error {I : Ideal R} {v w : SpecialLinearGroup ι R}
    (hv : mat v - 1 ∈ I.matrix ι) (hw : mat w - 1 ∈ I.matrix ι) :
    (mat ⁅v,w⁆ - 1) -
      ((mat v-1)*(mat w-1) - (mat w-1)*(mat v-1)) ∈ (I^3).matrix ι := by
  let D := (mat v-1)*(mat w-1) - (mat w-1)*(mat v-1)
  have hD : D ∈ (I^2).matrix ι := by
    simpa only [pow_two] using ((I*I).matrix ι).sub_mem
      (matrix_mul_mem hv hw) (matrix_mul_mem hw hv)
  have hD' : D = mat v * mat w - mat w * mat v := by
    dsimp [D]
    noncomm_ring
  have heq : (mat ⁅v,w⁆ - 1)-D = D * (mat (v⁻¹*w⁻¹)-1) := by
    rw [hD']
    simp only [commutatorElement_def, mat_mul]
    have hc : mat w * mat v * mat v⁻¹ * mat w⁻¹ = (1 : Matrix ι ι R) := by
      simp only [← mat_mul, mul_assoc, mul_inv_cancel, one_mul, mat_one]
    calc
      _ = (mat v*mat w-mat w*mat v)*(mat v⁻¹*mat w⁻¹) -
          (mat v*mat w-mat w*mat v) := by rw [sub_mul]; rw [← mul_assoc, ← mul_assoc, hc]
      _ = _ := by noncomm_ring
  rw [heq]
  simpa only [← pow_succ] using matrix_mul_mem hD
    (product_deviation (inv_deviation hv) (inv_deviation hw))

 

lemma nested_lie_mem_four {I : Ideal R} {u v w : SpecialLinearGroup ι R}
    (hu : mat u-1 ∈ I.matrix ι) (hv : mat v-1 ∈ I.matrix ι)
    (hw : mat w-1 ∈ I.matrix ι) (hrel : ⁅u,⁅v,w⁆⁆ = 1) :
    (mat u-1)*((mat v-1)*(mat w-1)-(mat w-1)*(mat v-1)) -
      ((mat v-1)*(mat w-1)-(mat w-1)*(mat v-1))*(mat u-1) ∈
      (I^4).matrix ι := by
  let D := (mat v-1)*(mat w-1)-(mat w-1)*(mat v-1)
  let C := mat ⁅v,w⁆ - 1
  have he : C-D ∈ (I^3).matrix ι := commutator_error hv hw
  have hc : (mat u-1)*C-C*(mat u-1) = 0 := by
    have h := congrArg (mat (R := R)) (commutatorElement_eq_one_iff_mul_comm.mp hrel)
    simp only [mat_mul] at h
    dsimp [C]
    noncomm_ring [h]
  have hm₁ : (mat u-1)*(C-D) ∈ (I^4).matrix ι := by
    simpa only [← pow_succ', show 3+1=4 by rfl] using matrix_mul_mem hu he
  have hm₂ : (C-D)*(mat u-1) ∈ (I^4).matrix ι := by
    simpa only [← pow_succ, show 3+1=4 by rfl] using matrix_mul_mem he hu
  have heq : (mat u-1)*D-D*(mat u-1) =
      -((mat u-1)*(C-D)-(C-D)*(mat u-1)) := by
    have hh : (mat u-1)*D-D*(mat u-1) +
        ((mat u-1)*(C-D)-(C-D)*(mat u-1)) = 0 := by
      calc
        _ = (mat u-1)*C-C*(mat u-1) := by noncomm_ring
        _ = 0 := hc
    exact eq_neg_of_add_eq_zero_left hh
  change (mat u-1)*D-D*(mat u-1) ∈ (I^4).matrix ι
  rw [heq]
  exact ((I^4).matrix ι).neg_mem (((I^4).matrix ι).sub_mem hm₁ hm₂)

end BoundaryOnly.Holonomy
namespace BoundaryOnly.Holonomy
open Matrix
open scoped BigOperators commutatorElement
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

abbrev lie (A B : Matrix ι ι R) := A * B - B * A

lemma lie_mem {I J : Ideal R} {A B : Matrix ι ι R}
    (hA : A ∈ I.matrix ι) (hB : B ∈ J.matrix ι) :
    lie A B ∈ (I*J).matrix ι := by
  apply ((I*J).matrix ι).sub_mem (matrix_mul_mem hA hB)
  simpa only [mul_comm J I] using matrix_mul_mem hB hA

lemma inverse_difference {I : Ideal R} {u v : SpecialLinearGroup ι R}
    (h : mat u - mat v ∈ I.matrix ι) :
    mat u⁻¹ - mat v⁻¹ ∈ I.matrix ι := by
  have he : mat u⁻¹ - mat v⁻¹ = -(mat u⁻¹ * (mat u - mat v) * mat v⁻¹) := by
    simp only [mul_sub, sub_mul, ← mat_mul, inv_mul_cancel,
      mat_one, one_mul, mul_inv_cancel_right, neg_sub]
  rw [he]
  exact (I.matrix ι).neg_mem (matrix_mul_right
    ((I.matrix ι).mul_mem_left _ h) _)

lemma conjugate_deviation (u v : SpecialLinearGroup ι R) :
    mat (u*v*u⁻¹)-1 = mat u*(mat v-1)*mat u⁻¹ := by
  simp only [mul_sub, sub_mul, mul_one, ← mat_mul, mul_inv_cancel, mat_one]

lemma conjugate_error {m N : Ideal R} {u U z : SpecialLinearGroup ι R}
    (hu : mat u-mat U ∈ m.matrix ι) (hz : mat z-1 ∈ N.matrix ι) :
    (mat (u*z*u⁻¹)-1) - mat U*(mat z-1)*mat U⁻¹ ∈ (m*N).matrix ι := by
  rw [conjugate_deviation]
  have he : mat u*(mat z-1)*mat u⁻¹ - mat U*(mat z-1)*mat U⁻¹ =
      (mat u-mat U)*(mat z-1)*mat u⁻¹ +
        mat U*(mat z-1)*(mat u⁻¹-mat U⁻¹) := by noncomm_ring
  rw [he]
  apply ((m*N).matrix ι).add_mem
  · exact matrix_mul_right (matrix_mul_mem hu hz) _
  · simpa only [mul_comm N m] using matrix_mul_mem
      ((N.matrix ι).mul_mem_left _ hz) (inverse_difference hu)

lemma lie_congruence {m N : Ideal R} {a b A B : Matrix ι ι R}
    (ha : a ∈ N.matrix ι) (hB : B ∈ N.matrix ι)
    (h₁ : a-A ∈ (m*N).matrix ι) (h₂ : b-B ∈ (m*N).matrix ι) :
    lie a b - lie A B ∈ (m*N^2).matrix ι := by
  have he : lie a b-lie A B = lie a (b-B)+lie (a-A) B := by
    dsimp [lie]; noncomm_ring
  rw [he]
  apply ((m*N^2).matrix ι).add_mem
  · simpa only [pow_two, mul_left_comm N m N, mul_assoc] using lie_mem ha h₂
  · simpa only [pow_two, mul_assoc] using lie_mem h₁ hB

lemma triple_congruence {m N : Ideal R} {a b c A B C : Matrix ι ι R}
    (ha : a ∈ N.matrix ι) (hB : B ∈ N.matrix ι) (hC : C ∈ N.matrix ι)
    (hb : b ∈ N.matrix ι)
    (h₁ : a-A ∈ (m*N).matrix ι) (h₂ : b-B ∈ (m*N).matrix ι)
    (h₃ : c-C ∈ (m*N).matrix ι) :
    lie a (lie b c)-lie A (lie B C) ∈ (m*N^3).matrix ι := by
  have he : lie a (lie b c)-lie A (lie B C) =
      lie a (lie b c-lie B C)+lie (a-A) (lie B C) := by
    dsimp [lie]; noncomm_ring
  rw [he]
  apply ((m*N^3).matrix ι).add_mem
  · have h := lie_mem ha (lie_congruence hb hC h₂ h₃)
    simpa only [mul_left_comm N m (N^2), ← pow_succ'] using h
  · have h := lie_mem h₁ (lie_mem hB hC)
    simpa only [← pow_two, mul_assoc, ← pow_succ'] using h

 

lemma reference_triple_mem {m N : Ideal R} (hNm : N ≤ m)
    {u v w U V W z t s : SpecialLinearGroup ι R}
    (hu : mat u-mat U ∈ m.matrix ι) (hv : mat v-mat V ∈ m.matrix ι)
    (hw : mat w-mat W ∈ m.matrix ι)
    (hz : mat z-1 ∈ N.matrix ι) (ht : mat t-1 ∈ N.matrix ι)
    (hs : mat s-1 ∈ N.matrix ι)
    (hrel : ⁅u*z*u⁻¹,⁅v*t*v⁻¹,w*s*w⁻¹⁆⁆=1) :
    lie (mat U*(mat z-1)*mat U⁻¹)
      (lie (mat V*(mat t-1)*mat V⁻¹) (mat W*(mat s-1)*mat W⁻¹)) ∈
        (m*N^3).matrix ι := by
  have hconj (a b : SpecialLinearGroup ι R) (hb : mat b-1 ∈ N.matrix ι) :
      mat (a*b*a⁻¹)-1 ∈ N.matrix ι := by
    rw [conjugate_deviation]
    exact matrix_mul_right ((N.matrix ι).mul_mem_left _ hb) _
  have hfour := nested_lie_mem_four (hconj u z hz) (hconj v t ht)
    (hconj w s hs) hrel
  have hp : N^4 ≤ m*N^3 := by
    rw [show 4=3+1 by rfl, pow_succ']
    exact Ideal.mul_mono hNm le_rfl
  have htop : lie (mat (u*z*u⁻¹)-1)
      (lie (mat (v*t*v⁻¹)-1) (mat (w*s*w⁻¹)-1)) ∈ (m*N^3).matrix ι :=
    fun i j ↦ hp (hfour i j)
  have herr := triple_congruence (hconj u z hz)
    (matrix_mul_right ((N.matrix ι).mul_mem_left (mat V) ht) (mat V⁻¹))
    (matrix_mul_right ((N.matrix ι).mul_mem_left (mat W) hs) (mat W⁻¹))
    (hconj v t ht) (conjugate_error hu hz) (conjugate_error hv ht)
    (conjugate_error hw hs)
  have h := ((m*N^3).matrix ι).sub_mem htop herr
  simpa only [sub_sub_cancel] using h

end BoundaryOnly.Holonomy
end

end OAI
