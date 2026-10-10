import Mathlib
import OAI.Probability.SKGap.Matrix.GOESparse
import OAI.Probability.SKGap.Matrix.TanhMatrixBounds

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

lemma coupling_symmetric (g : Disorder n) (i k : Fin n) : coupling g i k=coupling g k i := by
  by_cases h : i=k
  · subst k;rfl
  · rcases lt_or_gt_of_ne h with h | h <;> simp [coupling,h,not_lt_of_gt h]

lemma coupling_norm_from_goe (r d M : ℝ) (g : MatrixCoordinates (Fin n)→ℝ)
    (hd : 0 ≤ d) (hg : ‖matrixOperator (goeMatrix r g)‖ ≤ M)
    (hdiag : ∀ i,|goeMatrix r g i i| ≤ d) :
    ‖Matrix.of (coupling (goeDisorder r g))‖ ≤ M+d := by
  rw [coupling_goeDisorder]
  apply (norm_sub_le _ _).trans
  apply add_le_add _ (diagonal_norm_le hd _ hdiag)
  rwa [matrixOperator_eq_toEuclideanCLM,Matrix.l2_opNorm_toEuclideanCLM] at hg

lemma coupling_principal_norm_from_goe (r d ε : ℝ) (g : MatrixCoordinates (Fin n)→ℝ)
    (S : Finset (Fin n)) (hd : 0 ≤ d)
    (hg : principalOperatorNorm (goeMatrix r g) S ≤ ε)
    (hdiag : ∀ i,|goeMatrix r g i i| ≤ d) :
    ‖(Matrix.of (coupling (goeDisorder r g))).submatrix (fun i : S=>i.1) (fun i : S=>i.1)‖ ≤ ε+d := by
  rw [coupling_goeDisorder]
  have he : (goeMatrix r g-Matrix.diagonal (fun i=>goeMatrix r g i i)).submatrix
      (fun i : S=>i.1) (fun i : S=>i.1)=
      (goeMatrix r g).submatrix (fun i : S=>i.1) (fun i : S=>i.1)-
      Matrix.diagonal (fun i : S=>goeMatrix r g i.1 i.1) := by
    ext i k
    simp only [submatrix_apply,Matrix.sub_apply]
    congr 1
    simp only [Matrix.diagonal_apply,Subtype.val_inj]
  rw [he]
  apply (norm_sub_le _ _).trans
  have hb : ‖Matrix.diagonal (fun i : S=>goeMatrix r g i.1 i.1)‖ ≤ d :=
    diagonal_norm_le (ι:=S) hd _ (fun i=>hdiag i.1)
  apply add_le_add _ hb
  simpa only [principalOperatorNorm,matrixOperator_eq_toEuclideanCLM,Matrix.l2_opNorm_toEuclideanCLM] using hg

lemma row_square_restrict (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    {R : ℝ} (hr : ∀ i,∑ k,A i k^2 ≤ R) (i : S) :
    (∑ k : S,A i.1 k.1^2) ≤ R := by
  rw [Finset.sum_coe_sort S (fun k=>A i.1 k^2)]
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun k _ _=>sq_nonneg (A i.1 k))).trans (hr i.1)

lemma tanh_principal_norm (g : Disorder n) (S : Finset (Fin n)) {d R ε : ℝ}
    (hd : 0 ≤ d) (hR : 0 ≤ R)
    (hma : ∀ i k,|coupling g i k| ≤ d) (hrow : ∀ i,∑ k,coupling g i k^2 ≤ R)
    (hJ : ‖(Matrix.of (coupling g)).submatrix (fun i : S=>i.1) (fun i : S=>i.1)‖ ≤ ε) :
    ‖Matrix.of (fun i k : S=>tanh (coupling g i.1 k.1))‖ ≤ ε+d*R/3 := by
  let A : Matrix S S ℝ := (Matrix.of (coupling g)).submatrix (fun i : S=>i.1) (fun i : S=>i.1)
  have hh := tanh_matrix_remainder_norm A (fun i k=>coupling_symmetric g i.1 k.1)
    hR hd (fun i k=>hma i.1 k.1) (row_square_restrict _ S hrow)
  have he : Matrix.of (fun i k : S=>tanh (coupling g i.1 k.1))=
      A+(Matrix.of (fun i k=>tanh (A i k))-A) := by ext i k;simp [A]
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hJ hh)

lemma tanh_square_principal_norm (g : Disorder n) (S : Finset (Fin n)) {ε : ℝ}
    (hε : 0 ≤ ε) (hrows : ∀ i,∑ k∈S,coupling g i k^2 ≤ ε) :
    ‖Matrix.of (fun i k : S=>tanh (coupling g i.1 k.1)^2)‖ ≤ ε := by
  apply tanh_matrix_Q_norm (Matrix.of (fun i k : S=>coupling g i.1 k.1))
    (fun i k=>coupling_symmetric g i.1 k.1) hε
  intro i
  change (∑ k : S,coupling g i.1 k.1^2) ≤ ε
  rw [Finset.sum_coe_sort S (fun k=>coupling g i.1 k^2)]
  exact hrows i.1
end SKGap

end
end

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators
variable {n : ℕ}

lemma conditionalExpectation_flip (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i f (flip i x)=conditionalExpectation g h i f x := by
  simp only [conditionalExpectation,flip_flip]
  rw [add_comm (weight g h (flip i x)*f (flip i x)),add_comm (weight g h (flip i x))]

lemma conditionalExpectation_idem (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i (conditionalExpectation g h i f) x=conditionalExpectation g h i f x := by
  unfold conditionalExpectation at *
  rw [flip_flip]
  have hd : weight g h x+weight g h (flip i x) ≠ 0 := (add_pos (weight_pos _ _ _) (weight_pos _ _ _)).ne'
  have hd' : weight g h (flip i x)+weight g h x ≠ 0 := by simpa only [add_comm] using hd
  field_simp [hd,hd']
  ring

lemma expectation_flip_average (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (F : Spin n→ℝ) :
    expectation g h F=(1/2)*∑ x,(mass g h x*F x+mass g h (flip i x)*F (flip i x)) := by
  rw [Finset.sum_add_distrib,sum_flip i (fun x=>mass g h x*F x)]
  unfold expectation
  ring

lemma conditionalExpectation_adjoint (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f k : Spin n→ℝ) :
    expectation g h (fun x=>conditionalExpectation g h i f x*k x)=
    expectation g h (fun x=>f x*conditionalExpectation g h i k x) := by
  rw [expectation_flip_average g h i,expectation_flip_average g h i]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [conditionalExpectation_flip,conditionalExpectation_flip]
  unfold mass conditionalExpectation
  have hd : weight g h x+weight g h (flip i x) ≠ 0 := (add_pos (weight_pos _ _ _) (weight_pos _ _ _)).ne'
  have hZ := (partition_pos g h).ne'
  field_simp [hd,hZ]

lemma conditionalExpectation_mul_invariant (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f k : Spin n→ℝ) (hk : ∀ x,k (flip i x)=k x) (x : Spin n) :
    conditionalExpectation g h i (fun x=>f x*k x) x=conditionalExpectation g h i f x*k x := by
  unfold conditionalExpectation
  dsimp only
  rw [hk]
  ring

lemma conditionalExpectation_const (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (c : ℝ) (x : Spin n) : conditionalExpectation g h i (fun _=>c) x=c := by
  unfold conditionalExpectation
  have hd : weight g h x+weight g h (flip i x) ≠ 0 := (add_pos (weight_pos _ _ _) (weight_pos _ _ _)).ne'
  field_simp [hd]

lemma expectation_conditionalExpectation (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) : expectation g h (conditionalExpectation g h i f)=expectation g h f := by
  have he := conditionalExpectation_adjoint g h i f (fun _=>1)
  simpa only [conditionalExpectation_const,mul_one] using he

lemma expectation_projection_square (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) :
    expectation g h (fun x=>(f x-conditionalExpectation g h i f x)^2)=
      expectation g h (fun x=>f x*(f x-conditionalExpectation g h i f x)) := by
  have he := conditionalExpectation_adjoint g h i f (conditionalExpectation g h i f)
  simp only [conditionalExpectation_idem] at he
  have hp (x : Spin n) : (f x-conditionalExpectation g h i f x)^2=
      f x*(f x-conditionalExpectation g h i f x)+
      (conditionalExpectation g h i f x*conditionalExpectation g h i f x-
        f x*conditionalExpectation g h i f x) := by ring
  simp_rw [hp]
  rw [expectation_add,expectation_sub,he]
  ring

def heatBathGenerator (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) (x : Spin n) : ℝ :=
  ∑ i,(f x-conditionalExpectation g h i f x)

lemma expectation_sum (g : Disorder n) (h : Fin n→ℝ) {ι : Type*} [Fintype ι]
    (F : ι→Spin n→ℝ) : expectation g h (fun x=>∑ i,F i x)=∑ i,expectation g h (F i) := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma heatBathGenerator_form (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) :
    expectation g h (fun x=>f x*heatBathGenerator g h f x)=dirichlet g h f := by
  unfold heatBathGenerator dirichlet
  simp_rw [Finset.mul_sum]
  rw [expectation_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (expectation_projection_square g h i f).symm

lemma heatBathGenerator_adjoint (g : Disorder n) (h : Fin n→ℝ) (f k : Spin n→ℝ) :
    expectation g h (fun x=>heatBathGenerator g h f x*k x)=
      expectation g h (fun x=>f x*heatBathGenerator g h k x) := by
  unfold heatBathGenerator
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [expectation_sum,expectation_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [sub_mul,mul_sub]
  rw [expectation_sub,expectation_sub,conditionalExpectation_adjoint]

lemma conditionalDifference_zero_iff (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) : f x-conditionalExpectation g h i f x=0 ↔ f x=f (flip i x) := by
  have hd : weight g h x+weight g h (flip i x) ≠ 0 := (add_pos (weight_pos _ _ _) (weight_pos _ _ _)).ne'
  have hw := (weight_pos g h (flip i x)).ne'
  unfold conditionalExpectation
  rw [sub_eq_zero,eq_div_iff hd]
  constructor
  · intro hh
    have he : weight g h (flip i x)*(f x-f (flip i x))=0 := by nlinarith only [hh]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hw)
  · intro hh
    rw [hh]
    ring

lemma flip_invariant_constant (f : Spin n→ℝ) (hf : ∀ i x,f (flip i x)=f x) :
    ∀ x y,f x=f y := by
  classical
  intro x y
  have hs : ∀ S : Finset (Fin n),f (fun i=>if i∈S then y i else x i)=f x := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      let z : Spin n := fun k=>if k∈S then y k else x k
      have he : (fun k=>if k∈insert i S then y k else x k)=Function.update z i (y i) := by
        funext k
        by_cases hk : k=i
        · subst k;simp
        · simp [z,hk]
      rw [he]
      have hz : f (Function.update z i (y i))=f z := by
        by_cases hiy : y i=z i
        · rw [hiy,Function.update_eq_self]
        · have hnot : y i= !(z i) := by
            cases hy : y i <;> cases hz : z i <;> simp_all
          rw [hnot]
          exact hf i z
      exact hz.trans ih
  simpa using (hs Finset.univ).symm

lemma dirichlet_eq_zero_iff (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) :
    dirichlet g h f=0 ↔ ∀ x y,f x=f y := by
  constructor
  · intro hh
    have hi : ∀ i,expectation g h (fun x=>(f x-conditionalExpectation g h i f x)^2)=0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _=>expectation_nonneg g h (fun _=>sq_nonneg _))).mp hh i (Finset.mem_univ _)
    have hf : ∀ i x,f (flip i x)=f x := by
      intro i x
      have hx : mass g h x*(f x-conditionalExpectation g h i f x)^2=0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun y _=>mul_nonneg (mass_nonneg g h y) (sq_nonneg _))).mp
          (hi i) x (Finset.mem_univ _)
      have hd := (mul_eq_zero.mp hx).resolve_left (mass_pos g h x).ne'
      exact ((conditionalDifference_zero_iff g h i f x).mp (sq_eq_zero_iff.mp hd)).symm
    exact flip_invariant_constant f hf
  · intro hf
    unfold dirichlet
    apply Finset.sum_eq_zero
    intro i _
    have he : ∀ x,f x-conditionalExpectation g h i f x=0 := fun x=>(conditionalDifference_zero_iff g h i f x).mpr (hf x (flip i x))
    simp only [he,zero_pow (by omega : (2:ℕ) ≠ 0)]
    simp [expectation]
end SKGap

end
end

end OAI
