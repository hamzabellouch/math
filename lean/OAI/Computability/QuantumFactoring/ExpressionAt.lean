import Mathlib
import OAI.Computability.QuantumFactoring.ExpressionResources
import OAI.Computability.QuantumFactoring.NetworkAt
import OAI.Computability.QuantumFactoring.RetentionCircuit

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork

def NatExprAt {α : Type*} (len : α→ℕ) {v : α→Type*} (e : ∀x,NatExpr (v x)) :=
  PolyAt len (fun x=>(e x).weight)
namespace NatExprAt
variable {α : Type*} {len a b : α→ℕ} {v : α→Type*} {e : ∀x,NatExpr (v x)}
lemma ofPoly {v : ℕ→Type*} {e : ∀n,NatExpr (v n)} (he : NatExprPoly e) (len : α→ℕ) :
    NatExprAt len (fun x=>e (len x)) := PolyAt.ofPoly he len
lemma pull {β : Type*} (he : NatExprAt len e) (g : β→α) :
    NatExprAt (fun x=>len (g x)) (fun x=>e (g x)) := PolyAt.pull he g
lemma sharedCost (he : NatExprAt len e) : PolyAt len (fun x=>(e x).sharedCost) :=
  PolyAt.of_le he fun x=>(e x).sharedCost_le_weight
lemma templateWidth (he : NatExprAt len e) (hb : PolyAt len b) :
    PolyAt len (fun x=>(e x).templateWidth (b x)) :=
  PolyAt.of_le (((hb.add he).add (PolyAt.const len 1)).mul he)
    fun x=>(e x).templateWidth_le (b x)
lemma operationBound {f : α→ℕ} (hf : PolyAt len f) :
    PolyAt len (fun x=>NatExpr.operationBound (f x)) := by
  unfold NatExpr.operationBound
  poly_at
lemma template {vars : ∀x,v x→BooleanNetwork (a x) (b x)}
    (he : NatExprAt len e) (hb : PolyAt len b)
    (hv : ∃p : Polynomial ℕ,∀x i,(vars x i).net.count≤p.eval (len x)) :
    NetworkAt len (fun x=>(e x).template (vars x)) := by
  obtain ⟨p,hp⟩:=hv
  have hc : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  have hw:=he.templateWidth hb
  apply NetworkAt.of_le (he.sharedCost.mul (((operationBound hw).add hc).add hw))
  exact fun x=>(e x).template_shared_count (vars x) (hp x)
lemma isOne {vars : ∀x,v x→BooleanNetwork (a x) (b x)}
    (he : NatExprAt len e) (hb : PolyAt len b)
    (hv : ∃p : Polynomial ℕ,∀x i,(vars x i).net.count≤p.eval (len x)) :
    NetworkAt len (fun x=>(e x).isOne (vars x)) := by
  obtain ⟨p,hp⟩:=hv
  have hc : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  have hw:=he.templateWidth hb
  apply NetworkAt.of_le
    (((he.sharedCost.mul (((operationBound hw).add hc).add hw)).add
      ((PolyAt.const len 100).mul hw)).add (PolyAt.const len 21))
  exact fun x=>(e x).isOne_shared_count (vars x) (hp x)
end NatExprAt
end ExactQuantumFactoring

end


end OAI
