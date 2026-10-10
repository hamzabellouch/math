import Mathlib
import OAI.Combinatorics.UniformKServer.LiteralVector
import OAI.Combinatorics.UniformKServer.LiteralInput

namespace OAI

noncomputable section

namespace UniformKServer.LiteralBound
open Turing StackCompiler StackPrimitive
open scoped Classical

abbrev program := LiteralPartrec.processor LiteralVector.activeCode
abbrev Init (u r a : ℕ) := LiteralPartrec.input LiteralVector.activeCode [u,r,a]

def finishes (t u r a : ℕ) : Bool :=
  ((advance program)^[t] (ofState (Init u r a))).2.2

 theorem primitive_finishes : Primrec (fun p : ℕ×ℕ×ℕ×ℕ=>finishes p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold finishes
  exact Primrec.snd.comp (Primrec.snd.comp ((iter_primitive program).comp Primrec.fst
    ((LiteralInput.primitive_input LiteralVector.activeCode).comp (by fun_prop))))

 theorem finishes_run (t u r a : ℕ) :
    finishes t u r a=(run program (Init u r a) (List.replicate t false)).yielded := by
  have h:=ofState_run program (literal_deterministic LiteralVector.activeCode) (Init u r a) (List.replicate t false)
  simpa only [List.length_replicate,finishes,ofState] using congrArg (fun s=>s.2.2) h.symm

 theorem exists_time (u r a : ℕ) : ∃t,finishes t u r a=true := by
  let v : List.Vector ℕ 3:=⟨[u,r,a],rfl⟩
  have he : (RawProgram.run v).val∈Turing.ToPartrec.Code.eval LiteralVector.activeCode v.val := by
    rw [LiteralVector.active_eval]
    exact Part.mem_some _
  obtain ⟨t,ht,hs⟩:=LiteralPartrec.halts he
  exact ⟨t,by simpa only [finishes_run,v] using ht⟩

 theorem monotone_time {t T u r a : ℕ} (h : finishes t u r a=true) (ht : t≤T) :
    finishes T u r a=true := by
  rw [finishes_run] at h ⊢
  rw [capped_after program _ h ht]
  exact h

 theorem correct_at {t u r a : ℕ} (h : finishes t u r a=true) :
    ∀i,(run program (Init u r a) (List.replicate t false)).store i=
      ((Turing.PartrecToTM2.halt (RawProgram.run (⟨[u,r,a],rfl⟩ : List.Vector ℕ 3)).val).stk
        (FlatTM2.keys.symm i)).map FlatTM2.letters := by
  let v : List.Vector ℕ 3:=⟨[u,r,a],rfl⟩
  have he : (RawProgram.run v).val∈Turing.ToPartrec.Code.eval LiteralVector.activeCode v.val := by
    rw [LiteralVector.active_eval]
    exact Part.mem_some _
  obtain ⟨T,hT,hS⟩:=LiteralPartrec.halts he
  rw [finishes_run] at h
  have heq : run program (Init u r a) (List.replicate t false)=
      run program (Init u r a) (List.replicate T false) := by
    rcases le_total t T with ht|ht
    · exact (capped_after _ _ h ht).symm
    · exact capped_after _ _ hT ht
  rw [heq]
  exact hS

end UniformKServer.LiteralBound

end

end OAI
