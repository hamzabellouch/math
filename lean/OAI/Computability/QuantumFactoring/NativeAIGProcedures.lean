import Mathlib
import OAI.Computability.QuantumFactoring.BitStackListIndex
import OAI.Computability.QuantumFactoring.BitStackListLength
import OAI.Computability.QuantumFactoring.NativeAIGModel
import OAI.Computability.QuantumFactoring.BitStackAssociation

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure
abbrev refCode := prodCode Nat.bits boolCode
abbrev keyCode := prodCode refCode refCode
abbrev entryCode := prodCode keyCode Nat.bits
def declView : Decl→Unit⊕(ℕ⊕Key)
  | .zero=>.inl ()
  | .atom i=>.inr (.inl i)
  | .gate a b=>.inr (.inr (a,b))
def declCode (d : Decl) := sumCode emptyCode (sumCode Nat.bits keyCode) (declView d)
def graphCode (g : Graph) := prodCode (listCode declCode) (listCode entryCode) (g.decls,g.cache)

namespace Emission
open Procedure
noncomputable def refEq : Procedure (prodCode refCode refCode) boolCode
    (fun x=>decide (x.1=x.2)) := prodEq binaryEq (ofBool₂ boolCode fun a b=>decide (a=b))
noncomputable def keyEq : Procedure (prodCode keyCode keyCode) boolCode
    (fun x=>decide (x.1=x.2)) := prodEq refEq refEq
noncomputable def lookupP : Procedure (prodCode keyCode (listCode entryCode)) (optionCode Nat.bits)
    (fun x=>lookup x.1 x.2) :=
  (association ((0,false),(0,false)) 0 keyEq).congrFun (by
    rintro ⟨k,es⟩
    induction es with
    | nil=>rfl
    | cons e es ih=>simp only [assocLookup,lookup,ih])
noncomputable def decls : Procedure graphCode (listCode declCode) Graph.decls :=
  ((first (listCode declCode) (listCode entryCode)).precompose (fun g : Graph=>(g.decls,g.cache)))
noncomputable def cache : Procedure graphCode (listCode entryCode) Graph.cache :=
  ((second (listCode declCode) (listCode entryCode)).precompose (fun g : Graph=>(g.decls,g.cache)))
noncomputable def packGraph : Procedure (prodCode (listCode declCode) (listCode entryCode)) graphCode
    (fun x=>Graph.mk x.1 x.2) := (identity _).result (by intro x;rfl)
noncomputable def atomDecl : Procedure Nat.bits declCode Decl.atom :=
  (prepend Nat.bits [true,false]).result (by intro x;rfl)
noncomputable def gateDecl : Procedure keyCode declCode (fun x=>Decl.gate x.1 x.2) :=
  (prepend keyCode [true,true]).result (by intro x;rfl)
noncomputable def zeroDecl : Procedure declCode boolCode (fun x=>decide (x=Decl.zero)) :=
  ((casesSum (Procedure.constant emptyCode boolCode true)
    (Procedure.constant (sumCode Nat.bits keyCode) boolCode false)).precompose declView).congrFun
      (by intro x;cases x <;> rfl)
noncomputable def singleton {α : Type} (ea : α→List Bool) : Procedure ea (listCode ea) (fun a=>[a]) :=
  ((listCons ea).comp ((identity ea).pair (Procedure.constant ea (listCode ea) [])))
noncomputable def emptyP : Procedure emptyCode graphCode (fun _=>empty) :=
  Procedure.constant emptyCode graphCode empty
noncomputable def atomP : Procedure (prodCode graphCode Nat.bits) (prodCode graphCode refCode)
    (fun x=>atom x.1 x.2) := by
  let r:=first graphCode Nat.bits
  let i:=second graphCode Nat.bits
  let ds:=decls.comp r
  let cs:=cache.comp r
  let nd:=(listAppend declCode .zero).comp (ds.pair ((singleton declCode).comp (atomDecl.comp i)))
  let nr:=((listLength declCode .zero).comp ds).pair (Procedure.constant _ boolCode false)
  exact ((packGraph.comp (nd.pair cs)).pair nr).congrFun (by intro x;rfl)
noncomputable def addGateP : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode)
    (fun x=>addGate x.1 x.2.1 x.2.2) := by
  let r:=first graphCode keyCode
  let k:=second graphCode keyCode
  let ds:=decls.comp r
  let cs:=cache.comp r
  let sz:=(listLength declCode .zero).comp ds
  let nd:=(listAppend declCode .zero).comp (ds.pair ((singleton declCode).comp (gateDecl.comp k)))
  let nc:=(listCons entryCode).comp ((k.pair sz).pair cs)
  let nr:=sz.pair (Procedure.constant _ boolCode false)
  exact ((packGraph.comp (nd.pair nc)).pair nr).congrFun (by intro x;rfl)
noncomputable def constantP : Procedure (prodCode graphCode refCode) (optionCode boolCode)
    (fun x=>constant x.1 x.2) := by
  let r:=first graphCode refCode
  let a:=second graphCode refCode
  let idx:=(first Nat.bits boolCode).comp a
  let inv:=(second Nat.bits boolCode).comp a
  let d:=(listGet declCode .zero).comp (idx.pair (decls.comp r))
  exact (conditional (zeroDecl.comp d) ((optionSome boolCode).comp inv)
    (Procedure.constant _ (optionCode boolCode) none)).congrFun (by
      rintro ⟨g,⟨i,b⟩⟩
      simp only [Function.comp_apply,decide_eq_true_eq]
      have he : (g.decls.drop i).headD Decl.zero=g.decls[i]?.getD Decl.zero := by
        rw [List.headD_eq_head?_getD,List.head?_drop]
      rw [he]
      unfold constant
      cases g.decls[i]?.getD Decl.zero <;> simp)
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
