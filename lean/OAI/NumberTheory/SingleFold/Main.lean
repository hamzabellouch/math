import OAI.NumberTheory.SingleFold.RecursiveEnumeration

namespace OAI

namespace SingleFold
open Compiler

theorem recursively_enumerable_sf {n : ℕ} {p : (Fin n → ℕ) → Prop} (hp : REPred p) : SF p := by
  obtain ⟨Q,hQ,hD,M,hM⟩:=TM2Macro.exists_counter hp
  let := hQ
  let := hD
  have hc := CounterCompilation.halts_sf M
  have hi : MapSF (TM2Macro.counterInput (n:=n)) := by
    apply MapSF.vector
    intro j
    cases hs : TM2Macro.inputSlot j with
    | none => simpa only [TM2Macro.counterInput,hs,Option.elim_none] using (ScalarSF.const (α:=Fin n) 0)
    | some i => simpa only [TM2Macro.counterInput,hs,Option.elim_some] using ScalarSF.proj i
  exact (hi.pullback hc).congr (fun a=>(hM a).symm)

theorem main : MainStatement := by
  intro n _ S hS
  obtain ⟨r⟩:=recursively_enumerable_sf hS
  obtain ⟨m,hm,P,hP,hU⟩:=export_polynomial r
  exact ⟨m,hm,P,fun a=>⟨hP a,hU a⟩⟩
end SingleFold

end OAI
