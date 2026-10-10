import OAI.Combinatorics.PolynomialVacuum.Algebra.TraceClosing
import OAI.Combinatorics.PolynomialVacuum.Geometry.HoneycombVertex

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

noncomputable def finiteTensor (N : ℕ) (f : (Fin N → Spin) → ℂ) : SpinTensor ℕ ℂ :=
  fun s => f (fun j => s j.val)
noncomputable def rowKernel : (N : ℕ) → ℂ → (ℕ → ℂ) → (Fin N → Spin) →
    (Fin N → Spin) → Spin → Spin → ℂ
  | 0,_,_,_,_,a,b => if b=a then 1 else 0
  | N+1,c,X,out,inp,a,b => ∑ h : Spin,
      exchangeNumerator c (X 0) (out 0,h) (a,inp 0)*
        rowKernel N c (skipOne 0 X) (Fin.tail out) (Fin.tail inp) h b

@[simp] theorem headFiber_finiteTensor (N : ℕ) (f : (Fin (N+1) → Spin) → ℂ) (p : Spin) :
    headFiber p (finiteTensor (N+1) f)=finiteTensor N (fun s => f (Fin.cons p s)) := by
  funext s
  apply congrArg f
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [insertOne]
  · simp [insertOne]

theorem headFiber_auxiliary_gate (p a : Spin) (W : SpinTensor ℕ ℂ) (c x : ℂ) :
    headFiber p (siteR 0 c x (auxiliaryInput a W))=
      ∑ h : Spin, ∑ k : Spin,
        exchangeNumerator c x (p,h) (a,k) • auxiliaryInput h (headFiber k W) := by
  funext s
  simp only [headFiber,siteR,pairLinear,LinearMap.coe_mk,AddHom.coe_mk,pairAction,
    insertOne_self,insertOne_next,Fintype.sum_prod_type,auxiliaryInput,
    replacePair_left _ (by omega : (0 : ℕ)≠1) _,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  have he (b k : Spin) : skipOne 0 (replacePair (insertOne 0 p s) 0 1 (b,k))=
      insertOne 0 k (skipOne 0 s) := by
    funext j
    by_cases hj : j=0
    · subst j; simp [skipOne,replacePair,insertOne]
    · simp [skipOne,replacePair,insertOne,hj,
        show j-1+1=j by omega]
  simp_rw [he]
  simp

theorem skip_insertOne_succ {α : Type*} (N : ℕ) (b : α) (s : ℕ → α) :
    skipOne 0 (insertOne (N+1) b s)=insertOne N b (skipOne 0 s) := by
  funext j
  simp only [skipOne,not_lt_zero,ite_false,insertOne]
  split_ifs <;> first | rfl | (congr 1; omega)

 

theorem braidTrain_rowKernel (N : ℕ) (c : ℂ) (X : ℕ → ℂ)
    (f : (Fin N → Spin) → ℂ) (a b : Spin) (s : ℕ → Spin) :
    braidTrain c X 0 N (auxiliaryInput a (finiteTensor N f)) (insertOne N b s)=
      ∑ inp : Fin N → Spin,rowKernel N c X (fun j => s j.val) inp a b*f inp := by
  induction N generalizing X a b s with
  | zero =>
    simp only [braidTrain,Module.End.one_apply,auxiliaryInput,insertOne_self,finiteTensor,rowKernel,
      Finset.univ_unique,Finset.sum_singleton,ite_mul,one_mul,zero_mul]
    split_ifs <;> first | rfl | exact congrArg f (Subsingleton.elim _ _)
  | succ N ih =>
    rw [braidTrain,Module.End.mul_apply,braidTrain_head_evaluate,skip_insertOne_succ]
    have hs : insertOne (N+1) b s 0=s 0 := by simp [insertOne]
    rw [hs,headFiber_auxiliary_gate,map_sum]
    simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,headFiber_finiteTensor]
    simp_rw [ih]
    rw [← (Fin.consEquiv (fun _ : Fin (N+1) => Spin)).sum_comp]
    simp only [Fintype.sum_prod_type,Fin.consEquiv_apply,rowKernel,Fin.cons_zero]
    simp_rw [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro inp _
    apply Finset.sum_congr rfl
    intro h _
    have ht : (fun j : Fin N => skipOne 0 s j.val)=Fin.tail (fun j : Fin (N+1) => s j.val) := by
      funext j; simp [skipOne,Fin.tail]
    rw [ht]
    change _ = exchangeNumerator c (X 0) (s 0,h) (a,k)*
      rowKernel N c (skipOne 0 X) (Fin.tail (fun j : Fin (N+1) => s j.val)) inp h b*f (Fin.cons k inp)
    ring

noncomputable def transferMatrix (N : ℕ) (κ c : ℂ) (X : ℕ → ℂ) :
    Matrix (Fin N → Spin) (Fin N → Spin) ℂ :=
  fun out inp => ∑ h : Spin, κ^charge h * rowKernel N c X out inp h h

theorem tracedTrain_matrix (N : ℕ) (c : ℂ) (X : ℕ → ℂ)
    (f : (Fin N → Spin) → ℂ) (s : ℕ → Spin) :
    tracedTrain N c X (finiteTensor N f) s=
      ∑ inp : Fin N → Spin,transferMatrix N zeta c X (fun j => s j.val) inp*f inp := by
  simp only [tracedTrain,braidTrain_rowKernel,transferMatrix,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro inp _
  apply Finset.sum_congr rfl
  intro h _
  ring

end PolynomialVacuumAlgebra

end OAI
