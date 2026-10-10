import OAI.Combinatorics.PolynomialVacuum.Algebra.PrescriptionCollision
import OAI.Combinatorics.PolynomialVacuum.Algebra.TransportCovariance

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem swap_val {n : ℕ} (j : Fin n) (i : Fin (n+1)) :
    (Equiv.swap j.castSucc j.succ i).val=Equiv.swap j.val (j.val+1) i.val := by
  simp only [Equiv.swap_apply_def,Fin.ext_iff,Fin.val_castSucc,Fin.val_succ]
  split_ifs <;> rfl

theorem liftPolyTensor_rename_swap {N n : ℕ} (j : Fin n)
    (W : PolynomialTensor N (Fin (n+1))) (X : ℕ → ℂ) :
    liftPolyTensor (fun s => rename (Equiv.swap j.castSucc j.succ) (W s)) X=
      liftPolyTensor W (swapSite j.val X) := by
  funext s
  simp only [liftPolyTensor,eval_rename,Function.comp_apply,swapSite]
  congr 1
  apply congrArg eval
  funext k
  simp [swap_val]

theorem liftPolyTensor_ext {N m : ℕ} {V W : PolynomialTensor N (Fin m)}
    (h : ∀ X, liftPolyTensor V X=liftPolyTensor W X) : V=W := by
  funext s
  apply MvPolynomial.funext
  intro Z
  have hs := congrFun (h (extendFinite 0 Z)) (extendFinite Spin.zero s)
  simpa only [liftPolyTensor,extendFinite_fin] using hs

 

theorem cupPrescription_covariance {n : ℕ} (ψ : State n)
    (hψ : LowerExchange (liftState ψ) n) (i : Fin (n+1)) (j : Fin n) :
    tensorExchange (pairLeft j.castSucc) (pairRight j.castSucc)
      (X j.castSucc) (X j.succ) (cupPrescription ψ i)=
      fun s => ((C (t^2)*X j.castSucc-X j.succ)*(C T*X j.castSucc-X j.succ))*
        rename (Equiv.swap j.castSucc j.succ)
          (cupPrescription ψ (Equiv.swap j.castSucc j.succ i) s) := by
  apply liftPolyTensor_ext
  intro Xv
  rw [liftPolyTensor_exchange,liftPolyTensor_scalar,liftPolyTensor_rename_swap,
    cupPrescription_evaluation,cupPrescription_evaluation]
  simp only [eval_X,map_mul,map_sub,eval_C,swap_val]
  exact naturalPrescription_covariant (by omega : i.val ≤ n) j.isLt hψ Xv

theorem state_exchange_of_lower {n : ℕ} (ψ : State (n+1))
    (hψ : LowerExchange (liftState ψ) (n+1)) (j : Fin n) :
    tensorExchange j.castSucc j.succ (X j.castSucc) (X j.succ) ψ=
      fun s => ((C (t^2)*X j.castSucc-X j.succ)*(C T*X j.castSucc-X j.succ))*
        rename (Equiv.swap j.castSucc j.succ) (ψ s) := by
  apply liftPolyTensor_ext
  intro Xv
  rw [liftPolyTensor_exchange,liftPolyTensor_scalar,liftPolyTensor_rename_swap]
  simp only [eval_X,map_mul,map_sub,eval_C]
  exact hψ j.val (by omega) Xv

end PolynomialVacuumAlgebra

end OAI
