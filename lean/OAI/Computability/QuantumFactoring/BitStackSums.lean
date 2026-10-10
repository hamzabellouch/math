import Mathlib
import OAI.Computability.QuantumFactoring.BitStackChoice

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def sumCode {α β : Type} (ea : α→List Bool) (eb : β→List Bool) : α⊕β→List Bool
  | .inl a=>false::ea a
  | .inr b=>true::eb b

namespace Procedure
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool}
    {f : α→γ} {g : β→γ}
noncomputable def casesSum (p : Procedure ea ec f) (q : Procedure eb ec g) :
    Procedure (sumCode ea eb) ec (Sum.elim f g) where
  K:=(p.K ⊕ q.K) ⊕ Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inr 0
  program:=.cases (Sum.inr 0) .skip
    (p.shared.program.relabel (leftPublic p.K q.K))
    (q.shared.program.relabel (rightPublic p.K q.K))
  bound:=p.shared.bound+q.shared.bound+1
  runs x:=by
    cases x with
    | inl a=>
      have hpmono:=eval_nat_mono p.shared.bound (Nat.le_succ (ea a).length)
      obtain ⟨c,hc,hd⟩:=p.shared.runs a
      have hh:=hd.relabel (leftPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : leftPublic p.K q.K p.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨c+1,?_,?_⟩
      · rw [Polynomial.eval_add,Polynomial.eval_add,Polynomial.eval_one]
        exact Nat.add_le_add_right ((hc.trans hpmono).trans (Nat.le_add_right _ _)) 1
      · have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (false::ea a)) (Sum.inr 0) (ea a)=singletonStore (Sum.inr 0) (ea a):=by
          simp [singletonStore]
        simpa only [hu,sumCode] using Runs.cases_false (p:=Program.skip)
          (r:=q.shared.program.relabel (rightPublic p.K q.K))
          (xs:=ea a) (s:=singletonStore (Sum.inr 0) (false::ea a)) (by simp [singletonStore])
          (by rw [hu];exact hh)
    | inr b=>
      have hqmono:=eval_nat_mono q.shared.bound (Nat.le_succ (eb b).length)
      obtain ⟨c,hc,hd⟩:=q.shared.runs b
      have hh:=hd.relabel (rightPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : rightPublic p.K q.K q.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨c+1,?_,?_⟩
      · rw [Polynomial.eval_add,Polynomial.eval_add,Polynomial.eval_one]
        exact Nat.add_le_add_right ((hc.trans hqmono).trans (Nat.le_add_left _ _)) 1
      · have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (true::eb b)) (Sum.inr 0) (eb b)=singletonStore (Sum.inr 0) (eb b):=by
          simp [singletonStore]
        simpa only [hu,sumCode] using Runs.cases_true (p:=Program.skip)
          (q:=p.shared.program.relabel (leftPublic p.K q.K))
          (xs:=eb b) (s:=singletonStore (Sum.inr 0) (true::eb b)) (by simp [singletonStore])
          (by rw [hu];exact hh)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
