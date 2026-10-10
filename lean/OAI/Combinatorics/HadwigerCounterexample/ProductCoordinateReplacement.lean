import OAI.Combinatorics.HadwigerCounterexample.PairedRankBounds

namespace OAI

/-! # Product Coordinate Replacement -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function
open scoped BigOperators
variable {I J K : Type} {A : Type} [Fintype I] [DecidableEq I] [Fintype A]

set_option maxHeartbeats 600000 in
theorem update_avg (p : I→ Wgt A) (i : I) (f : Wgt (I→A)) (hp : IsLaw (p i)) :
    avg (prodW p) f = avg (prodW p) (fun x => avg (p i) (fun y => f (update x i y))) := by
  classical

  let e : ((I→A)×A)≃ ((I→A)×A) := {
    toFun x := (update x.1 i x.2,x.1 i)
    invFun x := (update x.1 i x.2,x.1 i)
    left_inv x := by simp
    right_inv x := by simp }
  let μ := pairW (prodW p) (p i)
  have he (x : (I→A)×A) : μ (e x)=μ x := by
    unfold μ pairW prodW
    let s := Finset.univ.erase i
    rw [←Finset.mul_prod_erase _ _ (mem_univ i),←Finset.mul_prod_erase _
      (fun i => p i (x.1 i)) (mem_univ i)]
    have h :
        ∏ j∈s,p j (update x.1 i x.2 j)=∏ j∈s,p j (x.1 j) := by
      refine prod_congr rfl fun j hj => ?_
      rw [update_of_ne ((mem_erase.mp hj).1)]
    change p i _ * (∏ j∈s,p j (update x.1 i x.2 j))*p i (x.1 i)=_
    rw [h]
    change p i (Function.update x.1 i (x.2) i) * _ * _=_
    rw [Function.update_self]; ac_rfl
  have ht := avg_bij e μ (fun x => f x.1)
  simp_rw [he] at ht
  unfold μ at ht; simp only [pairW_avg,hp.avg_const] at ht
  exact ht.symm

theorem update2_avg (p q : I→Wgt A) (i : I) (f : Wgt ((I→A)×(I→A))) (hp : IsLaw (p i))
    (hq : IsLaw (q i)) :
    let u := pairW (prodW p) (prodW q)
    avg u f = avg u (fun x => avg (pairW (p i) (q i))
      (fun y => f (update x.1 i y.1,update x.2 i y.2))) := by
  intro u
  simp only [u,pairW_avg]
  conv_lhs => rw [update_avg p i _ hp]
  apply avg_congr; intro x _

  conv_rhs => rw [avg_avg]
  exact avg_congr (fun _ _ => update_avg q i _ hq)
end HadwigerCounterexample

end

end OAI
