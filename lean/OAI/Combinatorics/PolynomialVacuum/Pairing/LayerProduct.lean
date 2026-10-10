import OAI.Combinatorics.PolynomialVacuum.Pairing.StackExpansion

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical
section
variable {S : Type*} [Fintype S] [DecidableEq S]

noncomputable def layerProduct {H : ℕ} (A : Fin H → Matrix S S ℂ) : Matrix S S ℂ :=
  (List.ofFn A).reverse.prod

@[simp] theorem layerProduct_cons {H : ℕ} (A : Matrix S S ℂ) (B : Fin H → Matrix S S ℂ) :
    layerProduct (Fin.cons A B)=layerProduct B*A := by
  simp [layerProduct,List.ofFn_succ]

@[simp] theorem layerProduct_const (H : ℕ) (A : Matrix S S ℂ) :
    layerProduct (fun _ : Fin H=>A)=A^H := by
  simp [layerProduct]

theorem layerProduct_append {H K : ℕ} (A : Fin H → Matrix S S ℂ) (B : Fin K → Matrix S S ℂ) :
    layerProduct (Fin.append A B)=layerProduct B*layerProduct A := by
  simp [layerProduct,List.ofFn_fin_append]

noncomputable def layerPathWeight {H : ℕ} (A : Fin H → Matrix S S ℂ) (inp : S) (r : Fin H → S) : ℂ :=
  ∏j : Fin H,A j (r j) ((Fin.cons inp r : Fin (H+1) → S) j.castSucc)

omit [Fintype S] [DecidableEq S] in
@[simp] theorem layerPathWeight_cons [Fintype S] [DecidableEq S] {H : ℕ}
    (A : Matrix S S ℂ) (B : Fin H → Matrix S S ℂ)
    (inp h : S) (r : Fin H → S) :
    layerPathWeight (Fin.cons A B) inp (Fin.cons h r)=A h inp*layerPathWeight B h r := by
  unfold layerPathWeight
  rw [Fin.prod_univ_succ]
  congr 1

 
theorem layerProduct_path_sum {H : ℕ} (A : Fin H → Matrix S S ℂ) (out inp : S) :
    layerProduct A out inp=∑r : Fin H → S,
      if matrixPathEnd inp r=out then layerPathWeight A inp r else 0 := by
  induction H generalizing out inp with
  | zero => simp [layerProduct,matrixPathEnd,layerPathWeight,Matrix.one_apply,eq_comm]
  | succ H ih =>
    have he : A=Fin.cons (A 0) (fun j=>A j.succ) := (Fin.cons_self_tail _).symm
    rw [he,layerProduct_cons,Matrix.mul_apply]
    simp_rw [ih]
    rw [← (Fin.consEquiv (fun _ : Fin (H+1)=>S)).sum_comp,Fintype.sum_prod_type]
    change _ = ∑h : S,∑r : Fin H → S,
      if matrixPathEnd inp (Fin.cons h r)=out then
        layerPathWeight (Fin.cons (A 0) (fun j=>A j.succ)) inp (Fin.cons h r) else 0
    simp only [Finset.sum_mul,matrixPathEnd_cons,layerPathWeight_cons]
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro r _
    split_ifs <;> simp [mul_comm]

 
theorem layerProduct_marked (H K : ℕ) (A B : Matrix S S ℂ) (d : S → ℂ) :
    layerProduct (Fin.append (fun _ : Fin H=>A)
      (Fin.cons (B*Matrix.diagonal d) (fun _ : Fin K=>B)))=
      B^(K+1)*Matrix.diagonal d*A^H := by
  rw [layerProduct_append,layerProduct_cons,layerProduct_const,layerProduct_const,pow_succ]
  simp only [Matrix.mul_assoc]

end
end PolynomialVacuumAlgebra

end OAI
