import OAI.Combinatorics.ThinTrees.Extraction

namespace OAI

universe uD uR uS

section

noncomputable section
open Matrix Polynomial Finset
namespace StrongThinTree.MSS
variable {D : Type uD} {R : Type uR} {S : Type uS} [Fintype D] [DecidableEq D] [CommRing R] [CommRing S]

def detLinear (M : Matrix D D R) : Matrix D D R →ₗ[R] R :=
  Matrix.detRowAlternating.toMultilinearMap.linearDeriv M

lemma detLinear_apply (M A : Matrix D D R) :
    detLinear M A=∑i, (Matrix.updateRow M i (A i)).det := by
  exact MultilinearMap.linearDeriv_apply _ M A

lemma detLinear_map (f : R →+* S) (M A : Matrix D D R) :
    detLinear (M.map f) (A.map f)=f (detLinear M A) := by
  simp only [detLinear_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [f.map_det]
  congr 1
  ext a b
  by_cases h : a=i <;> simp [Matrix.updateRow,Matrix.map_apply,Function.update,h]

lemma det_piecewise_mul (s : Finset D) (c : D → R) (A M : Matrix D D R) :
    Matrix.det (s.piecewise (fun i j => c i*A i j) M)=
      (∏i ∈ s, c i)*Matrix.det (s.piecewise A M) := by
  have he : s.piecewise (fun i j => c i*A i j) M=
      Matrix.of (fun i j => (if i ∈ s then c i else 1)*(s.piecewise A M) i j) := by
    ext i j
    by_cases hi : i ∈ s <;> simp [Finset.piecewise,hi]
  rw [he]
  have hh := Matrix.det_mul_column (fun i => if i ∈ s then c i else 1)
    (Matrix.of (s.piecewise A M))
  convert hh using 1 <;> try rfl
  exact congrArg (fun z => z*Matrix.det (s.piecewise A M)) (Finset.prod_ite_mem_eq s c).symm

lemma det_add_rankOne (M : Matrix D D R) (u v : D → R) :
    (M+Matrix.vecMulVec u v).det=M.det+detLinear M (Matrix.vecMulVec u v) := by
  have he := Matrix.detRowAlternating.toMultilinearMap.map_add_eq_map_add_linearDeriv_add
    M (Matrix.vecMulVec u v)
  change (M+Matrix.vecMulVec u v).det=M.det+detLinear M (Matrix.vecMulVec u v)+
    ∑s : Finset D with 2 ≤ s.card, Matrix.det (s.piecewise (Matrix.vecMulVec u v) M) at he
  rw [he]
  suffices hh : ∑s : Finset D with 2 ≤ s.card, Matrix.det (s.piecewise (Matrix.vecMulVec u v) M)=0 by
    rw [hh,add_zero]
  apply Finset.sum_eq_zero
  intro s hs
  have hc : 1 < s.card := by have hh := (Finset.mem_filter.mp hs).2; omega
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp hc
  change Matrix.det (s.piecewise (fun i j => u i*v j) M)=0
  rw [det_piecewise_mul s u (fun _ => v) M]
  have hz : Matrix.det (s.piecewise (fun _ : D => v) M)=0 := by
    apply Matrix.det_zero_of_row_eq hij
    simp [Finset.piecewise,hi,hj]
  rw [hz,mul_zero]

lemma det_linear_pencil_coeff_one (M A : Matrix D D R) :
    ((M.map Polynomial.C + (X : R[X]) • A.map Polynomial.C).det).coeff 1=detLinear M A := by
  have he := Matrix.detRowAlternating.toMultilinearMap.map_add_eq_map_add_linearDeriv_add
    (M.map Polynomial.C) ((X : R[X]) • A.map Polynomial.C)
  change (M.map Polynomial.C + (X : R[X]) • A.map Polynomial.C).det=
    (M.map Polynomial.C).det+detLinear (M.map Polynomial.C) ((X : R[X]) • A.map Polynomial.C)+
    ∑s : Finset D with 2 ≤ s.card,
      Matrix.det (s.piecewise ((X : R[X]) • A.map Polynomial.C) (M.map Polynomial.C)) at he
  rw [he,coeff_add,coeff_add]
  have hc : (M.map Polynomial.C).det=C M.det := (Polynomial.C.map_det M).symm
  rw [hc,map_smul,detLinear_map,smul_eq_mul,coeff_X_mul,coeff_C_zero,coeff_C]
  simp only [one_ne_zero,ite_false,zero_add]
  suffices hz : (∑s : Finset D with 2 ≤ s.card,
      Matrix.det (s.piecewise ((X : R[X]) • A.map Polynomial.C) (M.map Polynomial.C))).coeff 1=0 by
    rw [hz,add_zero]
  rw [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro s hs
  have hc : 2 ≤ s.card := (Finset.mem_filter.mp hs).2
  have hp : Matrix.det (s.piecewise ((X : R[X]) • A.map Polynomial.C) (M.map Polynomial.C))=
      (X : R[X])^s.card*Matrix.det (s.piecewise (A.map Polynomial.C) (M.map Polynomial.C)) := by
    rw [show (X : R[X]) • A.map Polynomial.C=fun i j => X*(A.map Polynomial.C) i j from rfl,
      det_piecewise_mul]
    simp
  rw [hp,coeff_X_pow_mul']
  simp [show ¬s.card ≤ 1 by omega]

end StrongThinTree.MSS

end
end

end OAI
