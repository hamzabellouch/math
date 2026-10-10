import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.OnlineTraverse
import OAI.Combinatorics.MatchingCount.Complexity.OnlineFrameCost
import OAI.Combinatorics.MatchingCount.Complexity.OnlineFoldCost

namespace OAI

namespace MatchingFPRAS.OnlineTree
open TreeTyped PhysicalStream Polynomial

variable {A B : Type} [Codec A] [Codec B]
lemma collectStep_cost {f : A→Experiment B} (F : Realizer f) (a : A) (bs : List B) :
    (collectStepRealizer F).cost (a,bs)=F.cost a+54*weight a+46*weight bs+
      26*(f a).worst weight+201 := by
  change (pair (composition (deterministic TreeTyped.first) F) (deterministic TreeTyped.second)).cost (a,bs)+
    (((f a).bind (fun b=>Experiment.done (b,bs))).worst (fun _=>1))=_
  rw [pair_cost,Experiment.worst_const]
  simp only [composition,deterministic,TreeTyped.first,TreeTyped.second,Experiment.worst,
    Experiment.bind,weight_prod]
  change (6*weight a+weight bs+11+F.cost a)+(3*weight a+7)+45*(1+weight a+weight bs)+
    26*(f a).worst weight+137+1=_
  omega

lemma traverse_bound {f : A→Experiment B} (F : Realizer f) :
    ∃ p : Polynomial ℕ,∀ as M,weight as≤M→(∀ a∈as,F.cost a+(f a).worst weight≤M)→
      (traverse F).cost as+(traverseM f as).worst weight≤p.eval M := by
  obtain ⟨q,hq⟩:=TreeTyped.polynomial_pair (TreeTyped.polynomial_identity (A:=List A))
    (TreeTyped.polynomial_constant ([] : List B))
  obtain ⟨r,hr⟩:=TreeTyped.polynomial_reverse (A:=B)
  let H : Polynomial ℕ := X*(X+1)+1
  let D : Polynomial ℕ := 27*X+54*X+46*H+201
  refine ⟨q+X*(D+14*X+34)+10+r.comp H+H,?_⟩
  intro as M hw ht
  have hl : as.length≤M := (list_length_le_weight as).trans hw
  have hH : H.eval M=M*(M+1)+1 := by simp [H]
  have hD : D.eval M=27*M+54*M+46*H.eval M+201 := by simp [D]
  have hf := fold_cost_bound (collectStep f) (collectStepRealizer F).cost as ([] : List B)
    (fun k bs=>weight bs+k*(M+1)≤as.length*(M+1)+1) (D.eval M) M
    (by simp; omega) hw
    (by
      intro a ha k _bounded bs hb
      rw [collectStep,Experiment.all_map]
      exact (Experiment.all_worst (f a) weight).mono (fun c hc=>by
        have hc':=ht a ha
        simp only [weight_cons,Nat.add_mul,Nat.one_mul] at *
        omega))
    (by
      intro a ha k _bounded bs hb
      rw [collectStep_cost]
      have ha':=(weight_mem ha).trans hw
      have hc':=ht a ha
      have hmul:=Nat.mul_le_mul_right (M+1) hl
      rw [hD,hH]
      omega)
  have hout : (foldM (collectStep f) as []).All (fun bs=>weight bs≤H.eval M) :=
    hf.2.mono (fun bs hb=>by
      have hmul:=Nat.mul_le_mul_right (M+1) hl
      rw [hH];simp only [Nat.zero_mul,Nat.add_zero] at hb;omega)
  have hrev : (foldM (collectStep f) as []).worst TreeTyped.reverse.cost≤r.eval (H.eval M) := by
    apply Experiment.worst_le _ _ _
    exact hout.mono (fun bs hb=>(Nat.le_add_right _ _).trans
      ((hr bs).trans (polynomial_eval_monotone r hb)))
  have hfinal : (traverseM f as).worst weight≤H.eval M := by
    apply Experiment.worst_le _ _ _
    apply Experiment.all_of_mean_eq (p:=(foldM (collectStep f) as []).map List.reverse)
      (fun h=>by
        rw [Experiment.mean_map,mean_fold_collect]
        simp only [List.append_nil,List.reverse_reverse]) _
    rw [Experiment.all_map]
    exact hout.mono (fun bs hb=>by simpa only [weight_reverse] using hb)
  have hpre:=(hq as).trans (polynomial_eval_monotone q hw)
  dsimp only at hpre
  have hmul:=Nat.mul_le_mul_right (D.eval M+14*M+34) hl
  change (TreeTyped.pair TreeTyped.identity (TreeTyped.constant ([] : List B))).cost as+
    Fold.cost (collectStep f) (collectStepRealizer F).cost as []+
    (foldM (collectStep f) as []).worst TreeTyped.reverse.cost+(traverseM f as).worst weight≤_
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_comp]
  omega

lemma work_traverse {f : A→Experiment B} {F : Realizer f} {m : A→ℕ} {n : List A→ℕ}
    (hF : WorkBound F m) (p q : Polynomial ℕ)
    (hw : ∀ as,weight as≤p.eval (n as)) (hm : ∀ as,∀ a∈as,m a≤q.eval (n as)) :
    WorkBound (traverse F) n := by
  obtain ⟨r,hr⟩:=hF
  obtain ⟨s,hs⟩:=traverse_bound F
  refine ⟨s.comp (p+r.comp q),fun as=>?_⟩
  simp only [Polynomial.eval_comp,Polynomial.eval_add]
  apply hs
  · exact (hw as).trans (Nat.le_add_right _ _)
  · intro a ha
    exact ((hr a).trans (polynomial_eval_monotone r (hm as a ha))).trans (Nat.le_add_left _ _)
lemma polynomial_traverse {f : A→Experiment B} {F : Realizer f} (hF : PolynomialTime F) :
    PolynomialTime (traverse F) := work_traverse hF X X (by simp) (by intro as a ha;simpa using weight_mem ha)
end MatchingFPRAS.OnlineTree

end OAI
