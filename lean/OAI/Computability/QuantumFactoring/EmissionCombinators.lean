import Mathlib
import OAI.Computability.QuantumFactoring.ExpressionSyntaxEmission

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
/-- Existence of a charged, clean, finite-alphabet stack procedure. -/
def Emits {α β : Type} (ea : α→List Bool) (eb : β→List Bool) (f : α→β) : Prop :=
  Nonempty (Procedure ea eb f)
namespace Emits
variable {α β γ δ : Type} {ea : α→List Bool} {eb : β→List Bool}
  {ec : γ→List Bool} {ed : δ→List Bool}
lemma ofProcedure {f : α→β} (p : Procedure ea eb f) : Emits ea eb f:=⟨p⟩
lemma id (e : α→List Bool) : Emits e e (fun x=>x):=⟨Procedure.identity e⟩
lemma const (ea : α→List Bool) (eb : β→List Bool) (b : β) : Emits ea eb (fun _=>b):=⟨Procedure.constant ea eb b⟩
lemma comp {f : α→β} {g : β→γ} (g' : Emits eb ec g) (f' : Emits ea eb f) :
    Emits ea ec (fun x=>g (f x)):=by
  obtain ⟨p⟩:=f';obtain ⟨q⟩:=g';exact ⟨q.comp p⟩
lemma pair {f : α→β} {g : α→γ} (h : Emits ea eb f) (j : Emits ea ec g) :
    Emits ea (prodCode eb ec) (fun x=>(f x,g x)):=by
  obtain ⟨p⟩:=h;obtain ⟨q⟩:=j;exact ⟨p.pair q⟩
lemma fst {f : α→β×γ} (h : Emits ea (prodCode eb ec) f) : Emits ea eb (fun x=>(f x).1):=
  (ofProcedure (Procedure.first eb ec)).comp h
lemma snd {f : α→β×γ} (h : Emits ea (prodCode eb ec) f) : Emits ea ec (fun x=>(f x).2):=
  (ofProcedure (Procedure.second eb ec)).comp h
lemma congr {f g : α→β} (h : Emits ea eb f) (hh : ∀x,f x=g x) : Emits ea eb g:=by
  obtain ⟨p⟩:=h;exact ⟨p.congrFun hh⟩
lemma precompose {f : β→γ} (h : Emits eb ec f) (g : α→β) : Emits (fun x=>eb (g x)) ec (fun x=>f (g x)):=by
  obtain ⟨p⟩:=h;exact ⟨p.precompose g⟩
lemma natAdd {f g : α→ℕ} (h : Emits ea Nat.bits f) (j : Emits ea Nat.bits g) :
    Emits ea Nat.bits (fun x=>f x+g x):=(ofProcedure Procedure.binaryAdd).comp (h.pair j)
lemma natSub {f g : α→ℕ} (h : Emits ea Nat.bits f) (j : Emits ea Nat.bits g) :
    Emits ea Nat.bits (fun x=>f x-g x):=(ofProcedure Procedure.binarySub).comp (h.pair j)
lemma natMul {f g : α→ℕ} (h : Emits ea Nat.bits f) (j : Emits ea Nat.bits g) :
    Emits ea Nat.bits (fun x=>f x*g x):=(ofProcedure Procedure.binaryMul).comp (h.pair j)
lemma natDiv {f g : α→ℕ} (h : Emits ea Nat.bits f) (j : Emits ea Nat.bits g) :
    Emits ea Nat.bits (fun x=>f x/g x):=(ofProcedure Procedure.binaryDiv).comp (h.pair j)
lemma natMod {f g : α→ℕ} (h : Emits ea Nat.bits f) (j : Emits ea Nat.bits g) :
    Emits ea Nat.bits (fun x=>f x%g x):=(ofProcedure Procedure.binaryMod).comp (h.pair j)
lemma natMax {f g : α→ℕ} (h : Emits ea Nat.bits f) (j : Emits ea Nat.bits g) :
    Emits ea Nat.bits (fun x=>max (f x) (g x)):=(ofProcedure NetworkEmission.Emission.binaryMax).comp (h.pair j)
lemma unaryNat {f : α→ℕ} (h : Emits ea unaryCode f) : Emits ea Nat.bits f:=
  (ofProcedure Procedure.unaryToBits).comp h
end Emits
end ExactQuantumFactoring.BitStackProgram

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace Emits
variable {α v : Type} {ea : α→List Bool} {ev : v→List Bool}
lemma nvar {f : α→v} (h : BitStackProgram.Emits ea ev f) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>NatExpr.var (f x)):=
  (ofProcedure (Emission.exprVarP ev)).comp h
lemma nconst {f : α→ℕ} (h : BitStackProgram.Emits ea Nat.bits f) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>NatExpr.const (f x)):=
  (ofProcedure (Emission.exprConstP ev)).comp h
lemma nadd {f g : α→NatExpr v} (h : BitStackProgram.Emits ea (exprCode ev) f)
    (j : BitStackProgram.Emits ea (exprCode ev) g) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>NatExpr.add (f x) (g x)):=
  (ofProcedure (Emission.exprAddP ev)).comp (h.pair j)
lemma nsub {f g : α→NatExpr v} (h : BitStackProgram.Emits ea (exprCode ev) f)
    (j : BitStackProgram.Emits ea (exprCode ev) g) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>NatExpr.sub (f x) (g x)):=
  (ofProcedure (Emission.exprSubP ev)).comp (h.pair j)
lemma nmul {f g : α→NatExpr v} (h : BitStackProgram.Emits ea (exprCode ev) f)
    (j : BitStackProgram.Emits ea (exprCode ev) g) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>NatExpr.mul (f x) (g x)):=
  (ofProcedure (Emission.exprMulP ev)).comp (h.pair j)
lemma ndiv {f g : α→NatExpr v} (h : BitStackProgram.Emits ea (exprCode ev) f)
    (j : BitStackProgram.Emits ea (exprCode ev) g) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>NatExpr.div (f x) (g x)):=
  (ofProcedure (Emission.exprDivP ev)).comp (h.pair j)
lemma nmod {f g : α→NatExpr v} (h : BitStackProgram.Emits ea (exprCode ev) f)
    (j : BitStackProgram.Emits ea (exprCode ev) g) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>NatExpr.mod (f x) (g x)):=
  (ofProcedure (Emission.exprModP ev)).comp (h.pair j)
lemma nite {a b c d : α→NatExpr v} (ha : BitStackProgram.Emits ea (exprCode ev) a)
    (hb : BitStackProgram.Emits ea (exprCode ev) b)
    (hc : BitStackProgram.Emits ea (exprCode ev) c)
    (hd : BitStackProgram.Emits ea (exprCode ev) d) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>NatExpr.iteLe (a x) (b x) (c x) (d x)):=
  (ofProcedure (Emission.exprIteP ev)).comp (ha.pair (hb.pair (hc.pair hd)))
end Emits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
