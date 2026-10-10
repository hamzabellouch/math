import Mathlib
import OAI.Computability.QuantumFactoring.NetworkPredicateEmission

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α v : Type} {ea : α→List Bool} {n w b : α→ℕ}
lemma compileFinite {k : ℕ} (en : Fin k ≃ v) {e : α→NatExpr v}
    (he : BitStackProgram.Emits ea (exprCode (fun i:v=>(en.symm i).val.bits)) e)
    (hn : BitStackProgram.Emits ea unaryCode n) (hw : BitStackProgram.Emits ea unaryCode w)
    {fs : ∀x,v→BooleanNetwork (n x) (w x)} (hf : ∀i,NetEmits ea (fun x=>fs x i)) :
    NetEmits ea (fun x=>(e x).compile (fs x)):=by
  classical
  choose p hp ep using hf
  let ps (x:α):=List.ofFn (fun i=>p (en i) x)
  have hps : BitStackProgram.Emits ea (listCode packCode) ps:=BitStackProgram.Emits.ofFn (fun i=>hp (en i))
  let out (x:α):=exprPack (n x) (w x) (fun i:v=>Emission.envVars (ps x) (en.symm i).val) (e x)
  refine ⟨out,(ofProcedure (Emission.genericExprPackP (fun i:v=>(en.symm i).val))).comp
    ((hn.pair (hw.pair hps)).pair he),?_⟩
  intro x
  apply exprPack_value
  intro i
  have hh : Emission.envVars (ps x) (en.symm i).val=p i x:=by
    simp [Emission.envVars,ps,List.headD_eq_head?_getD,List.head?_drop,(en.symm i).isLt]
  rw [hh];exact ep i x
lemma templateFinite {k : ℕ} (en : Fin k ≃ v) {e : α→NatExpr v}
    (he : BitStackProgram.Emits ea (exprCode (fun i:v=>(en.symm i).val.bits)) e)
    (hn : BitStackProgram.Emits ea unaryCode n) (hb : BitStackProgram.Emits ea unaryCode b)
    {fs : ∀x,v→BooleanNetwork (n x) (b x)} (hf : ∀i,NetEmits ea (fun x=>fs x i)) :
    NetEmits ea (fun x=>(e x).template (fs x)):=by
  have hw : BitStackProgram.Emits ea unaryCode (fun x=>(e x).templateWidth (b x)):=
    (ofProcedure (Emission.exprWidthP _)).comp (hb.pair he)
  exact compileFinite en he hn hw (fun i=>(hf i).comp (resize hb hw))
lemma isOneFinite {k : ℕ} (en : Fin k ≃ v) {e : α→NatExpr v}
    (he : BitStackProgram.Emits ea (exprCode (fun i:v=>(en.symm i).val.bits)) e)
    (hn : BitStackProgram.Emits ea unaryCode n) (hb : BitStackProgram.Emits ea unaryCode b)
    {fs : ∀x,v→BooleanNetwork (n x) (b x)} (hf : ∀i,NetEmits ea (fun x=>fs x i)) :
    NetEmits ea (fun x=>(e x).isOne (fs x)):=by
  have hw : BitStackProgram.Emits ea unaryCode (fun x=>(e x).templateWidth (b x)):=
    (ofProcedure (Emission.exprWidthP _)).comp (hb.pair he)
  exact (templateFinite en he hn hb hf).equalOn (wordConst hn hw (const _ _ 1)) hw
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
