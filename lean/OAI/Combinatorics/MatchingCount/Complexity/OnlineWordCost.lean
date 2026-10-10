import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.OnlineWord
import OAI.Combinatorics.MatchingCount.Complexity.OnlineFrameCost
import OAI.Combinatorics.MatchingCount.Complexity.OnlineFoldCost

namespace OAI

namespace MatchingFPRAS.OnlineWord
open TreeTyped OnlineTree PhysicalStream Polynomial

lemma polynomial_step : OnlineTree.PolynomialTime stepRealizer := by
  unfold stepRealizer
  apply OnlineTree.work_congr
  apply OnlineTree.polynomial_choose <;> apply OnlineTree.polynomial_deterministic <;>
    apply TreeTyped.polynomial_composition <;> first | exact TreeTyped.polynomial_listCons |
      exact TreeTyped.polynomial_pair (TreeTyped.polynomial_constant _) TreeTyped.polynomial_second

lemma weight_bools (bs : List Bool) : weight bs≤4*bs.length+1 := by
  induction bs with
  | nil => simp
  | cons b bs ih => have hb:=TreeTyped.weight_bool b; simp only [weight_cons,List.length_cons];omega
lemma all_weight (n : ℕ) (acc : List Bool) :
    (prepend n acc).All (fun bs=>weight bs≤4*(n+acc.length)+1) :=
  (all_length n acc).mono (fun bs hb=>by rw [←hb]; exact weight_bools bs)

lemma polynomial_list : OnlineTree.PolynomialTime listRealizer := by
  obtain ⟨p,hp⟩:=polynomial_step
  have prep := TreeTyped.polynomial_pair (TreeTyped.polynomial_identity (A:=List ℕ))
    (TreeTyped.polynomial_constant ([] : List Bool))
  obtain ⟨q,hq⟩:=prep
  refine ⟨q+X*((p.comp (5*X+2))+14*X+34)+4*X+11,fun as=>?_⟩
  let S:=weight as
  have hlen : as.length≤S := list_length_le_weight as
  have bound := OnlineTree.fold_cost_bound step stepRealizer.cost as ([] : List Bool)
    (fun k bs=>bs.length+k=as.length) (p.eval (5*S+2)) S (by simp) le_rfl
    (by
      intro a ha k hk bs hb
      simp only [step,Experiment.All,List.length_cons]
      constructor <;> omega)
    (by
      intro a ha k hk bs hb
      have ha' : weight a≤S := weight_mem ha
      have hbs:=weight_bools bs
      have hw : weight (a,bs)≤5*S+2 := by rw [weight_prod];omega
      exact (Nat.le_add_right _ _).trans ((hp (a,bs)).trans (polynomial_eval_monotone p hw)))
  have hlenmul := Nat.mul_le_mul_right (p.eval (5*S+2)+14*S+34) hlen
  have hout := Experiment.worst_le _ _ _ (all_weight as.length [])
  have hpre:=hq as
  change (TreeTyped.pair TreeTyped.identity (TreeTyped.constant ([] : List Bool))).cost as+
    OnlineTree.Fold.cost step stepRealizer.cost as []+(prepend as.length []).worst weight≤_
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_X,Polynomial.eval_ofNat]
  dsimp [S] at *
  omega

lemma work_natural : OnlineTree.WorkBound naturalRealizer (fun n=>n+weight n) := by
  apply OnlineTree.work_congr
  apply OnlineTree.work_then_polynomial _ polynomial_list
  exact OnlineTree.work_deterministic (TreeTyped.work_remeasure TreeTyped.range_numeric_work X (fun n=>by simp))
end MatchingFPRAS.OnlineWord

end OAI
