import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGProcedures

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG.Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def optionTrue : Procedure (optionCode boolCode) boolCode
    (fun x=>x=some true) :=
  (optionGet boolCode false).congrFun (by intro x;cases x with
    | none=>rfl
    | some b=>cases b <;> rfl)
noncomputable def optionFalse : Procedure (optionCode boolCode) boolCode
    (fun x=>x=some false) :=
  (optionCases (Procedure.constant emptyCode boolCode false) boolNot).congrFun
    (by intro x;cases x with
    | none=>rfl
    | some b=>cases b <;> rfl)
noncomputable def goP : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode)
    (fun x=>go x.1 x.2.1 x.2.2) := by
  let r:=first graphCode keyCode
  let k:=second graphCode keyCode
  let a:=(first refCode refCode).comp k
  let b:=(second refCode refCode).comp k
  let ca:=constantP.comp (r.pair a)
  let cb:=constantP.comp (r.pair b)
  let lk:=lookupP.comp (k.pair (cache.comp r))
  let z:=r.pair (Procedure.constant _ refCode (0,false))
  let ra:=r.pair a
  let rb:=r.pair b
  let cm:=(binaryEq.comp (((first Nat.bits boolCode).comp a).pair
    ((first Nat.bits boolCode).comp b)))
  let ci:=((ofBool₂ boolCode (fun a b=>decide (a=b))).comp
    (((second Nat.bits boolCode).comp a).pair ((second Nat.bits boolCode).comp b)))
  let twins:=conditional cm (conditional ci ra z) addGateP
  let rest:=conditional (boolOr.comp ((optionFalse.comp ca).pair (optionFalse.comp cb))) z
    (conditional (optionTrue.comp ca) rb (conditional (optionTrue.comp cb) ra twins))
  let hit:=r.pair (((optionGet Nat.bits 0).comp lk).pair (Procedure.constant _ boolCode false))
  exact (conditional ((optionIsSome Nat.bits).comp lk) hit rest).congrFun (by
    rintro ⟨g,⟨a,b⟩⟩
    simp only [Function.comp_apply]
    unfold go
    cases hl : lookup (a,b) g.cache with
    | some i=>simp
    | none=>
      simp only [Option.isSome_none,Bool.false_eq_true,↓reduceIte,Bool.or_eq_true,decide_eq_true_eq]
      cases ha : constant g a with
      | none=>
        cases hb : constant g b with
        | none=>simp
        | some bb=>cases bb <;> simp
      | some aa=>cases aa <;> cases hb : constant g b with
        | none=>simp
        | some bb=>cases bb <;> simp)
noncomputable def gateP : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode)
    (fun x=>gate x.1 x.2.1 x.2.2) := by
  let r:=first graphCode keyCode
  let k:=second graphCode keyCode
  let a:=(first refCode refCode).comp k
  let b:=(second refCode refCode).comp k
  let t:=binaryLt.comp (((first Nat.bits boolCode).comp a).pair ((first Nat.bits boolCode).comp b))
  exact (conditional t goP (goP.comp (r.pair (b.pair a)))).congrFun
    (by intro x;simp only [Function.comp_apply,decide_eq_true_eq,gate])
end ExactQuantumFactoring.NativeAIG.Emission

end



end OAI
