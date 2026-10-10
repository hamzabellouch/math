import Mathlib
import OAI.Computability.QuantumFactoring.BitStackComposition
import OAI.Computability.QuantumFactoring.BitStackQuotation
import OAI.Computability.QuantumFactoring.BitStackFrames

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def prodCode {α β : Type} (ea : α→List Bool) (eb : β→List Bool) (x : α×β) : List Bool :=
  pairBits (ea x.1) (eb x.2)

namespace Procedure
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool} {f : α→β}

/-- Run a procedure on the first component, keeping the second component
literally on a disjoint stack. Parsing and re-quoting are explicitly charged. -/
noncomputable def left (p : Procedure ea eb f) (ec : γ→List Bool) :
    Procedure (prodCode ea ec) (prodCode eb ec) (fun x=>(f x.1,x.2)) where
  K:=p.K ⊕ Fin 3
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inr 0
  program:=.seq (unquoteMove (Sum.inr 0) (Sum.inl p.input) (Sum.inr 1) (Sum.inr 2))
    (.seq (p.program.relabel Sum.inl)
      (quoteMove (Sum.inl p.output) (Sum.inr 0) (Sum.inr 1)))
  bound:=Polynomial.C 14*Polynomial.X+Polynomial.C 8*p.bound+Polynomial.C 11
  runs x:=by
    obtain ⟨cp,hcp,hp⟩:=p.runs x.1
    let s : Store (p.K ⊕ Fin 3):=singletonStore (Sum.inr 0) (prodCode ea ec x)
    let u : Store (p.K ⊕ Fin 3):=sumStore (singletonStore p.input (ea x.1))
      (singletonStore 0 (ec x.2))
    let v : Store (p.K ⊕ Fin 3):=sumStore (singletonStore p.output (eb (f x.1)))
      (singletonStore 0 (ec x.2))
    have hparse : Runs (unquoteMove (Sum.inr 0) (Sum.inl p.input) (Sum.inr 1) (Sum.inr 2))
        s u (7*(ea x.1).length+6) := by
      have hh:=unquoteMove_runs (Sum.inr 0 : p.K ⊕ Fin 3) (Sum.inl p.input)
        (Sum.inr 1) (Sum.inr 2) (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp) (ea x.1) (ec x.2) s (by simp [s,singletonStore,prodCode,pairBits])
        (by simp [s,singletonStore]) (by simp [s,singletonStore])
      convert hh using 1
      funext k
      cases k with
      | inl k => by_cases hk : k=p.input <;> simp_all [s,u,singletonStore,sumStore,Function.update]
      | inr k => fin_cases k <;> simp [s,u,singletonStore,sumStore,Function.update]
    have hcall : Runs (p.program.relabel Sum.inl) u v cp := hp.left (singletonStore (0 : Fin 3) (ec x.2))
    have hquote : Runs (quoteMove (Sum.inl p.output) (Sum.inr 0) (Sum.inr 1)) v
        (singletonStore (Sum.inr 0) (pairBits (eb (f x.1)) (ec x.2)))
        (7*(eb (f x.1)).length+5) := by
      have hh:=quoteMove_runs (Sum.inl p.output : p.K ⊕ Fin 3)
        (Sum.inr 0) (Sum.inr 1) (by simp) (by simp) (by simp) v (by simp [v,singletonStore])
      convert hh using 1
      · funext k
        cases k with
        | inl k => by_cases hk : k=p.output <;>
            simp_all [v,singletonStore,sumStore,Function.update]
        | inr k => fin_cases k <;> simp [v,singletonStore,sumStore,Function.update,pairBits]
      · simp [v,singletonStore]
    refine ⟨(7*(eb (f x.1)).length+5)+cp+(7*(ea x.1).length+6),?_,
      Runs.seq hparse (Runs.seq hcall hquote)⟩
    have hlen:=p.output_length_le x.1
    have hx : (ea x.1).length≤(prodCode ea ec x).length := by
      simp only [prodCode,pairBits_length]; omega
    have hm:=eval_nat_mono p.bound hx
    dsimp only at hm
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega

/-- Exchange two quoted word fields, without a unit-cost tuple operation. -/
noncomputable def swap (ea : α→List Bool) (eb : β→List Bool) :
    Procedure (prodCode ea eb) (prodCode eb ea) Prod.swap where
  K:=Fin 4
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=1
  program:=.seq (unquoteMove 0 1 2 3) (quoteMove 0 1 2)
  bound:=Polynomial.C 7*Polynomial.X+Polynomial.C 11
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
    have h2 : Runs (quoteMove 0 1 2) u (singletonStore 1 (prodCode eb ea x.swap))
        (7*(eb x.2).length+5) := by
      have hh:=quoteMove_runs (0 : Fin 4) 1 2 (by decide) (by decide) (by decide) u
        (by simp [u,singletonStore])
      convert hh using 1
      · funext k; fin_cases k <;> simp [u,singletonStore,Function.update,prodCode,pairBits]
      · simp [u,singletonStore]
    refine ⟨(7*(eb x.2).length+5)+(7*(ea x.1).length+6),?_,Runs.seq h1 h2⟩
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      prodCode,pairBits_length]
    omega

/-- Two arbitrary already verified subroutines acting independently on a pair. -/
noncomputable def parallel {δ : Type} {ed : δ→List Bool} {g : γ→δ}
    (p : Procedure ea eb f) (q : Procedure ec ed g) :
    Procedure (prodCode ea ec) (prodCode eb ed) (fun x=>(f x.1,g x.2)) :=
  (((swap ed eb).comp ((q.left eb).comp ((swap eb ec).comp (p.left ec)))).congrFun
    (by intro x; rfl))
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
