import OAI.MathematicalPhysics.Heisenberg.SlotOnMesh

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix
namespace Heisenberg.TensorUnits
variable {R E K : Type*} [CommSemiring R] [Semiring E] [Algebra R E]
  [Fintype K] [DecidableEq K]

lemma ofFn_prod_eq_single {n : ℕ} (f : Fin n → E) (i : Fin n)
    (h : ∀ j,j≠i → f j=1) : (List.ofFn f).prod=f i := by
  induction n with
  | zero=>exact Fin.elim0 i
  | succ n ih=>
    induction i using Fin.cases with
    | zero=>
      rw [List.ofFn_succ,List.prod_cons]
      have he : (fun j : Fin n=>f j.succ)=fun _=>1 := by
        funext j
        exact h _ (Fin.succ_ne_zero j)
      rw [he,List.ofFn_const,List.prod_replicate,one_pow,mul_one]
    | succ i=>
      rw [List.ofFn_succ,List.prod_cons,h 0 (Ne.symm (Fin.succ_ne_zero i)),one_mul]
      exact ih (fun j=>f j.succ) i (fun j hj=>h _ (fun he=>hj (Fin.succ_injective _ he)))

lemma lift_onsiteFin {n : ℕ} (u : Fin n → K → K → E)
    (hs : ∀ i,∑ a,u i a a=1) (i : Fin n) (M : Matrix K K R) :
    liftLinear (system u) (TensorMatrix.onsite i M)=liftLinear (u i) M := by
  unfold TensorMatrix.onsite TensorMatrix.tensor
  rw [lift_tensorFin]
  have he:=ofFn_prod_eq_single (fun j=>liftLinear (u j) (Function.update (fun _ : Fin n=>(1:Matrix K K R)) i M j)) i
    (fun j hj=>by rw [Function.update_of_ne hj,lift_one (u j) (hs j)])
  simpa only [Function.update_self] using he

variable {X : Type*} [Fintype X] [DecidableEq X]

def functionReindex {n : ℕ} (e : X ≃ Fin n) : (X → K) ≃ (Fin n → K) where
  toFun f:=f ∘ e.symm
  invFun f:=f ∘ e
  left_inv f:=by ext x; simp
  right_inv f:=by ext x; simp

omit [Fintype K] [DecidableEq K] [DecidableEq X] in
lemma reindex_tensor {n : ℕ} (e : X ≃ Fin n) (M : X → Matrix K K R) :
    Matrix.reindex (functionReindex e) (functionReindex e) (TensorMatrix.tensor M)=
      TensorMatrix.tensor (fun i=>M (e.symm i)) := by
  ext a b
  change (∏ x,M x (a (e x)) (b (e x)))=∏ i,M (e.symm i) (a i) (b i)
  simpa only [Equiv.apply_symm_apply] using (e.symm.prod_comp (fun x=>M x (a (e x)) (b (e x)))).symm

omit [Fintype K] in
lemma reindex_onsite {n : ℕ} (e : X ≃ Fin n) (x : X) (M : Matrix K K R) :
    Matrix.reindex (functionReindex e) (functionReindex e) (TensorMatrix.onsite x M)=
      TensorMatrix.onsite (e x) M := by
  unfold TensorMatrix.onsite
  rw [reindex_tensor]
  congr 1
  ext i a b
  by_cases hi : i=e x
  · subst i; simp
  · have hx : e.symm i≠x:=fun hh=>hi (by rw [←hh,Equiv.apply_symm_apply])
    simp [Function.update_of_ne hi,Function.update_of_ne hx]

end Heisenberg.TensorUnits
end
end

end OAI
