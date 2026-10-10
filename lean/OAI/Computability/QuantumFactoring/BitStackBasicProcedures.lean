import Mathlib
import OAI.Computability.QuantumFactoring.BitStackProducts

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool}
  {f : α→β} {g : α→γ}

/-- Duplicate the input word and quote the first copy to represent a pair. -/
noncomputable def duplicate (ea : α→List Bool) :
    Procedure ea (prodCode ea ea) (fun a=>(a,a)) where
  K:=Fin 4
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=3
  program:=.seq (duplicateReverse 0 1 2) (.seq (reverseMove 1 3) (quoteMove 0 3 1))
  bound:=Polynomial.C 14*Polynomial.X+Polynomial.C 8
  runs a:=by
    let s : Store (Fin 4):=singletonStore 0 (ea a)
    let u : Store (Fin 4):=Function.update s 1 (ea a).reverse
    let v : Store (Fin 4):=Function.update s 3 (ea a)
    have h1 : Runs (duplicateReverse 0 1 2) s u (5*(ea a).length+2) := by
      have hh:=duplicateReverse_runs (0 : Fin 4) 1 2 (by decide) (by decide) (by decide)
        s (by simp [s,singletonStore])
      simpa only [u,s,singletonStore,Function.update_self,
        Function.update_of_ne (by decide : (1 : Fin 4)≠0),List.append_nil] using hh
    have h2 : Runs (reverseMove 1 3) u v (2*(ea a).length+1) := by
      have hh:=reverseMove_runs (1 : Fin 4) 3 (by decide) u
      convert hh using 1
      · funext k; fin_cases k <;> simp [u,v,s,singletonStore,Function.update]
      · simp [u]
    have h3 : Runs (quoteMove 0 3 1) v
        (singletonStore 3 (prodCode ea ea (a,a))) (7*(ea a).length+5) := by
      have hh:=quoteMove_runs (0 : Fin 4) 3 1 (by decide) (by decide) (by decide) v
        (by simp [v,s,singletonStore])
      convert hh using 1
      · funext k; fin_cases k <;> simp [v,s,singletonStore,Function.update,prodCode,pairBits]
      · simp [v,s,singletonStore]
    refine ⟨(7*(ea a).length+5)+(2*(ea a).length+1)+(5*(ea a).length+2),?_,
      Runs.seq h1 (Runs.seq h2 h3)⟩
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega

noncomputable def pair (p : Procedure ea eb f) (q : Procedure ea ec g) :
    Procedure ea (prodCode eb ec) (fun a=>(f a,g a)) :=
  (p.parallel q).comp (duplicate ea)

/-- Projection parses the actual prefix code and explicitly clears its tail. -/
noncomputable def first (ea : α→List Bool) (eb : β→List Bool) :
    Procedure (prodCode ea eb) ea Prod.fst where
  K:=Fin 4
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=1
  program:=.seq (unquoteMove 0 1 2 3) (clear 0)
  bound:=Polynomial.C 7*Polynomial.X+Polynomial.C 7
  runs x:=by
    let s : Store (Fin 4):=singletonStore 0 (prodCode ea eb x)
    let u : Store (Fin 4):=Function.update (singletonStore 0 (eb x.2)) 1 (ea x.1)
    have h1 : Runs (unquoteMove 0 1 2 3) s u (7*(ea x.1).length+6) := by
      have hh:=unquoteMove_runs (0 : Fin 4) 1 2 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (ea x.1) (eb x.2) s
        (by simp [s,singletonStore,prodCode,pairBits])
        (by simp [s,singletonStore]) (by simp [s,singletonStore])
      convert hh using 1
      funext k; fin_cases k <;> simp [s,u,singletonStore,Function.update]
    have h2 : Runs (clear 0) u (singletonStore 1 (ea x.1)) (2*(eb x.2).length+1) := by
      have hh:=clear_runs (0 : Fin 4) u
      convert hh using 1
      · funext k; fin_cases k <;> simp [u,singletonStore,Function.update]
      · simp [u,singletonStore]
    refine ⟨(2*(eb x.2).length+1)+(7*(ea x.1).length+6),?_,Runs.seq h1 h2⟩
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      prodCode,pairBits_length]
    omega

noncomputable def second (ea : α→List Bool) (eb : β→List Bool) :
    Procedure (prodCode ea eb) eb Prod.snd :=
  ((first eb ea).comp (swap ea eb)).congrFun (by intro x; rfl)

end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
