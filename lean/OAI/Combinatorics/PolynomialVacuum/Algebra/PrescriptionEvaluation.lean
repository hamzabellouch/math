import OAI.Combinatorics.PolynomialVacuum.Algebra.FiniteLift
import OAI.Combinatorics.PolynomialVacuum.Algebra.SpectatorList

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem braidList_cons (c : ℂ) (X : ℕ → ℂ) (k : ℕ) (ks : List ℕ) :
    braidList c X (k::ks)=braidList c X ks*siteR k c (X k) := by
  unfold braidList
  rw [List.foldl_cons,braidList_fold]
  rfl

theorem liftPolyTensor_transport {n : ℕ} (i : Fin (n+1)) (ks : List (Fin (n+1)))
    (W : PolynomialTensor (n+2) (Fin (n+1))) (X : ℕ → ℂ) :
    liftPolyTensor (transportCup i ks W) X=
      braidList (T*X i.val) X (ks.map Fin.val) (liftPolyTensor W X) := by
  induction ks generalizing W with
  | nil => simp [transportCup,braidList]
  | cons k ks ih =>
    change liftPolyTensor (transportCup i ks
      (tensorExchange (pairLeft k) (pairRight k) (C T*MvPolynomial.X i) (MvPolynomial.X k) W)) X=_
    rw [ih,liftPolyTensor_exchange]
    simp only [map_mul,eval_C,eval_X,List.map_cons,braidList_cons,Module.End.mul_apply]
    rfl

theorem eval_leftFusionFactors {n : ℕ} (i : Fin (n+1)) (X : ℕ → ℂ) :
    eval (fun k : Fin (n+1) => X k.val) (leftFusionFactors i)=leftFusion i.val X := by
  simp only [leftFusionFactors,leftFusion,fusionPair,map_prod,map_mul,map_sub,eval_X,eval_C]
  apply Finset.prod_bij (fun k _ => k.val)
  · intro k hk
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
  · intro a ha b hb hab
    exact Fin.ext hab
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    refine ⟨⟨k,by have hi:=i.isLt; omega⟩,?_,rfl⟩
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact hk'
  · intro k hk
    rfl

theorem liftPolyTensor_scalar {N m : ℕ} (p : MvPolynomial (Fin m) ℂ)
    (W : PolynomialTensor N (Fin m)) (X : ℕ → ℂ) :
    liftPolyTensor (fun s => p*W s) X=
      eval (fun k : Fin m => X k.val) p • liftPolyTensor W X := by
  funext s
  simp [liftPolyTensor]

 

theorem cupPrescription_evaluation {n : ℕ} (ψ : State n) (i : Fin (n+1)) (X : ℕ → ℂ) :
    liftPolyTensor (cupPrescription ψ i) X=naturalPrescription (liftState ψ) n i.val X := by
  change liftPolyTensor (fun s => (C (1+T)*MvPolynomial.X i*leftFusionFactors i)*
      transportCup i (rightSpectators i) (initialCup ψ i) s) X=_
  rw [liftPolyTensor_scalar,liftPolyTensor_transport,rightSpectators_val,braidList_range,
    liftPolyTensor_initialCup]
  simp only [map_mul,eval_C,eval_X,eval_leftFusionFactors,naturalPrescription,Module.End.mul_apply]

end PolynomialVacuumAlgebra

end OAI
