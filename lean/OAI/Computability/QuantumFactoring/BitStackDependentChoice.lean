import Mathlib
import OAI.Computability.QuantumFactoring.EmissionCombinators

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {f : α→β}
noncomputable def chooseBitD (c : α→Prop) [DecidablePred c]
    (p : Procedure (fun x:{a // ¬c a}=>ea x.val) eb (fun x=>f x.val))
    (q : Procedure (fun x:{a // c a}=>ea x.val) eb (fun x=>f x.val)) :
    Procedure (fun a=>decide (c a)::ea a) eb f where
  K:=(p.K ⊕ q.K) ⊕ Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inr 0
  program:=.cases (Sum.inr 0) .skip
    (p.shared.program.relabel (leftPublic p.K q.K))
    (q.shared.program.relabel (rightPublic p.K q.K))
  bound:=p.shared.bound+q.shared.bound+1
  runs a:=by
    have hpmono:=eval_nat_mono p.shared.bound (Nat.le_succ (ea a).length)
    have hqmono:=eval_nat_mono q.shared.bound (Nat.le_succ (ea a).length)
    by_cases h:c a
    · obtain ⟨t,ht,hd⟩:=q.shared.runs ⟨a,h⟩
      have hh:=hd.relabel (rightPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : rightPublic p.K q.K q.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨t+1,?_,?_⟩
      · simpa only [List.length_cons,Polynomial.eval_add,Polynomial.eval_one] using
          Nat.add_le_add_right ((ht.trans hqmono).trans (Nat.le_add_left
            (q.shared.bound.eval ((ea a).length+1)) (p.shared.bound.eval ((ea a).length+1)))) 1
      · simp only [h,decide_true]
        have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (true::ea a)) (Sum.inr 0) (ea a)=singletonStore (Sum.inr 0) (ea a):=by
          simp [singletonStore]
        simpa only [hu] using Runs.cases_true (p:=Program.skip)
          (q:=p.shared.program.relabel (leftPublic p.K q.K))
          (xs:=ea a) (s:=singletonStore (Sum.inr 0) (true::ea a)) (by simp [singletonStore])
          (by rw [hu];exact hh)
    · obtain ⟨t,ht,hd⟩:=p.shared.runs ⟨a,h⟩
      have hh:=hd.relabel (leftPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : leftPublic p.K q.K p.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨t+1,?_,?_⟩
      · simpa only [List.length_cons,Polynomial.eval_add,Polynomial.eval_one] using
          Nat.add_le_add_right ((ht.trans hpmono).trans (Nat.le_add_right
            (p.shared.bound.eval ((ea a).length+1)) (q.shared.bound.eval ((ea a).length+1)))) 1
      · simp only [h,decide_false]
        have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (false::ea a)) (Sum.inr 0) (ea a)=singletonStore (Sum.inr 0) (ea a):=by
          simp [singletonStore]
        simpa only [hu] using Runs.cases_false (p:=Program.skip)
          (r:=q.shared.program.relabel (rightPublic p.K q.K))
          (xs:=ea a) (s:=singletonStore (Sum.inr 0) (false::ea a)) (by simp [singletonStore])
          (by rw [hu];exact hh)
noncomputable def splitOn (c : α→Prop) [DecidablePred c]
    (test : Procedure ea boolCode (fun a=>decide (c a)))
    (yes : Procedure (fun x:{a // c a}=>ea x.val) eb (fun x=>f x.val))
    (no : Procedure (fun x:{a // ¬c a}=>ea x.val) eb (fun x=>f x.val)) : Procedure ea eb f:=by
  let p:=no.comp (unprefix (fun x:{a // ¬c a}=>ea x.val) false)
  let q:=yes.comp (unprefix (fun x:{a // c a}=>ea x.val) false)
  let choice:=(chooseBitD c p q).comp (unprefix (fun a=>decide (c a)::false::ea a) true)
  let input:= (test.pair (identity ea)).result (ec:=fun a=>true::decide (c a)::false::ea a)
    (h:=id) (by intro a;rfl)
  exact choice.comp input
end ExactQuantumFactoring.BitStackProgram.Procedure

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {f : α→β}
lemma splitOn (c : α→Prop) [DecidablePred c]
    (test : Emits ea Procedure.boolCode (fun a=>decide (c a)))
    (yes : Emits (fun x:{a // c a}=>ea x.val) eb (fun x=>f x.val))
    (no : Emits (fun x:{a // ¬c a}=>ea x.val) eb (fun x=>f x.val)) : Emits ea eb f:=by
  obtain ⟨p⟩:=test;obtain ⟨q⟩:=yes;obtain ⟨r⟩:=no
  exact ⟨Procedure.splitOn c p q r⟩
end ExactQuantumFactoring.BitStackProgram.Emits

end



end OAI
