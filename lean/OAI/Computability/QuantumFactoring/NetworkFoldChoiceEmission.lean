import Mathlib
import OAI.Computability.QuantumFactoring.RawTrialFieldsEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
lemma foldChoice_budget (c : Pack) (xs : List Pack) (b : Pack) :
    (xs.foldl (fun b a=>compPack (pairPack a b) c) b).val.budget=
      b.val.budget+(xs.map (fun a=>a.val.budget)).sum+c.val.budget*xs.length:=by
  exact fold_budget_extra _ c.val.budget (by intros;rfl) _ _
lemma foldChoice_state (xs : List Pack) (c b : Pack) :
    xs.foldl (fun s a=>(s.1,compPack (pairPack a s.2) s.1)) (c,b)=
      (c,xs.foldl (fun b a=>compPack (pairPack a b) c) b):=by
  induction xs generalizing b with
  | nil=>rfl
  | cons a xs ih=>simpa only [List.foldl_cons] using ih (compPack (pairPack a b) c)
lemma quadBudget_bound (a b c d A B N : ℕ) (ha : a≤A) (hb : b≤B)
    (hd : d≤N) (hc : c≤N) :
    2*(104*(a+1)^2)+104*(b+c+a*d+1)^2+1 ≤ 1000*(N+2*A+B+1+1)^4:=by
  let T:=N+2*A+B+1
  have he : a≤T := by dsimp [T];omega
  have ht : d≤T := by dsimp [T];omega
  have hs0 : b+c≤T := by dsimp [T];omega
  have hs : b+c+a*d+1≤(T+1)^2:=by
    have hm:=Nat.mul_le_mul he ht
    nlinarith only [hs0,hm]
  have hh:=Nat.pow_le_pow_left hs 2
  have hh':=Nat.pow_le_pow_left (show a+1≤T+1 by omega) 2
  have hp4 : ((T+1)^2)^2=(T+1)^4:=by ring
  rw [hp4] at hh
  have h24 : (T+1)^2≤(T+1)^4:=Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1≤(T+1)^4:=Nat.one_le_pow _ _ (Nat.succ_pos _)
  have h2:=(hh'.trans h24)
  change _ ≤ 1000*(T+1)^4
  omega
lemma foldChoice_code_bound (xs : List Pack) (a : Pack×Pack) (i : ℕ) :
    (prodCode packCode packCode ((xs.take i).foldl (fun s a=>(s.1,compPack (pairPack a s.2) s.1)) a)).length ≤
      1000*((listCode packCode xs).length+(prodCode packCode packCode a).length+1)^4:=by
  rw [show a=(a.1,a.2) from rfl,foldChoice_state]
  simp only [prodCode,pairBits_length]
  have hc:=packCode_bound a.1
  have hb:=packCode_bound ((xs.take i).foldl (fun b t=>compPack (pairPack t b) a.1) a.2)
  rw [foldChoice_budget] at hb
  have ha:=packBudget_le_code a.1
  have ha':=packBudget_le_code a.2
  have hx:=(packBudgets_le_code (xs.take i)).trans (listCode_length_take_le packCode i xs)
  have hl:=(list_length_le_code packCode (xs.take i)).trans (listCode_length_take_le packCode i xs)
  have H:=quadBudget_bound _ _ _ _ _ _ _ ha ha' hl hx
  calc
    _ ≤ 2*(104*(a.1.val.budget+1)^2)+104*(a.2.val.budget+((xs.take i).map (fun t=>t.val.budget)).sum+a.1.val.budget*(xs.take i).length+1)^2+1 := by omega
    _ ≤ _ := by simpa only [Nat.add_assoc] using H
namespace Emission
noncomputable def foldChoiceStepP : Procedure (prodCode packCode (prodCode packCode packCode))
    (prodCode packCode packCode) (fun x=>(x.2.1,compPack (pairPack x.1 x.2.2) x.2.1)):=by
  let ex:=first packCode (prodCode packCode packCode)
  let st:=second packCode (prodCode packCode packCode)
  let sc:=(first packCode packCode).comp st
  let sb:=(second packCode packCode).comp st
  exact sc.pair (compPackP.comp ((pairPackP.comp (ex.pair sb)).pair sc))
noncomputable def foldChoiceP : Procedure
    (prodCode (listCode packCode) (prodCode packCode packCode)) packCode
    (fun x=>x.1.foldr (fun a b=>compPack (pairPack a b) x.2.1) x.2.2):=by
  let fold:=foldList emptyPack foldChoiceStepP
    (Polynomial.C 1000*(Polynomial.X+1)^4) (by
      intro xs a i
      simpa only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
        using foldChoice_code_bound xs a i)
  let inp:=((listReverse packCode emptyPack).comp (first (listCode packCode) (prodCode packCode packCode))).pair
    (second (listCode packCode) (prodCode packCode packCode))
  exact ((second packCode packCode).comp (fold.comp inp)).congrFun (by
    intro x;change (x.1.reverse.foldl (fun s a=>(s.1,compPack (pairPack a s.2) s.1)) x.2).2 = _
    rw [show x.2=(x.2.1,x.2.2) from rfl,foldChoice_state];exact List.foldl_reverse)
end Emission
namespace NetEmits
open BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {n w K : α→ℕ}
lemma minimumChoice (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>OrderTrial.minimumChoice (w x)):=by
  have hl:=left hw hw
  have hr:=right hw hw
  have hz:=wordConst (hw.unaryAdd hw) hw (const _ _ 0)
  exact (hl.equalOn hz hw).wordMux hr ((hr.equalOn hz hw).wordMux hl ((hl.wordLt hr hw).wordMux hl hr hw) hw) hw
lemma minimum {f : ∀x,Fin (K x)→BooleanNetwork (n x) (w x)}
    (hn : Emits ea unaryCode n) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>OrderTrial.minimumNet (f x)):=by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨q,hq,eq⟩:=extendPack hK p hp
  obtain ⟨pp⟩:=hq
  have hps:=(ofProcedure (Procedure.tabulate (f:=q) emptyPack pp)).comp (hK.pair (id ea))
  obtain ⟨c,hc,ec⟩:=minimumChoice hw
  obtain ⟨b,hb,eb⟩:=wordConst hn hw (const _ _ 0)
  refine ⟨fun x=>((List.range (K x)).map (q x)).foldr (fun a b=>compPack (pairPack a b) (c x)) (b x),
    (ofProcedure Emission.foldChoiceP).comp (hps.pair (hc.pair hb)),?_⟩
  intro x
  dsimp only
  rw [←ofFn_nat_eq_map]
  have hh:∀j (g:Fin j→BooleanNetwork (n x) (w x)) (ps:Fin j→Pack),
      (∀i,(ps i).val.value=erase (g i))→
      ((List.ofFn ps).foldr (fun a b=>compPack (pairPack a b) (c x)) (b x)).val.value=erase (OrderTrial.minimumNet g):=by
    intro j;induction j with
    | zero=>intro g ps h;simpa only [List.ofFn_zero,List.foldr_nil,OrderTrial.minimumNet] using eb x
    | succ j ih=>
      intro g ps h
      rw [List.ofFn_succ,List.foldr_cons,OrderTrial.minimumNet]
      exact compPack_spec _ _ _ _ (pairPack_spec _ _ _ _ (h 0) (ih _ _ (fun i=>h i.succ))) (ec x)
  exact hh _ _ _ (fun i=>by rw [eq];exact he ⟨x,i⟩)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
