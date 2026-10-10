import Mathlib
import OAI.Computability.MinUncut.Estimates.Bridge

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer.LocalTemplate
open MinUncut.Inner MinUncut.Costed
open MinUncutGames.Foundations.Hastad.SourceOccurrences

def signatureEquiv (t : ℕ) : Signature (Fin t) ≃
    ((Fin t → F₂) × (Fin t → Fin 3 → Fin 3 → Bool)) where
  toFun s := (s.rhs,s.same)
  invFun p := ⟨p.1,p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def signatureEncoding (t : ℕ) : Encoding (Signature (Fin t)) :=
  let a := ((Encoding.fin t).function fieldEncoding).prod
    ((Encoding.fin t).function ((Encoding.fin 3).function ((Encoding.fin 3).function Encoding.bool)))
  ⟨a.size,(signatureEquiv t).trans a.code⟩

def signatureNumber {t : ℕ} (s : Signature (Fin t)) : ℕ :=
  (∑i : Fin t,(∑p : Fin 3,(∑q : Fin 3,(s.same i p q).toNat*2^q.val)*(2^3)^p.val)*((2^3)^3)^i.val)+
    ((2^3)^3)^t*(∑i : Fin t,(s.rhs i).val*2^i.val)

lemma bool_code (b : Bool) : (Encoding.bool.code b).val=b.toNat := by cases b <;> rfl

lemma signature_code {t : ℕ} (s : Signature (Fin t)) :
    ((signatureEncoding t).code s).val=signatureNumber s := by
  change (∑i : Fin t,(∑p : Fin 3,(∑q : Fin 3,(Encoding.bool.code (s.same i p q)).val*2^q.val)*(2^3)^p.val)*((2^3)^3)^i.val)+_=_
  simp only [bool_code,signatureNumber]
  rfl

def constantTable {α : Type} (e : Encoding α) (f : α → ℕ) : List (ℕ × ℕ) :=
  e.enumerate.map (fun a=>((e.code a).val,f a))

lemma lookupValue_mem {xs : List (ℕ × ℕ)} (hn : (xs.map Prod.fst).Nodup)
    {i x : ℕ} (h : (i,x)∈xs) : AExpr.lookupValue i xs=x := by
  induction xs with
  | nil => simp at h
  | cons p xs ih =>
    rcases p with ⟨j,y⟩
    simp only [List.map_cons,List.nodup_cons] at hn
    rcases List.mem_cons.mp h with h|h
    · cases h
      simp [AExpr.lookupValue]
    · have hij : i≠j := by
        intro he
        subst i
        exact hn.1 (List.mem_map.mpr ⟨(j,x),h,rfl⟩)
      simp only [AExpr.lookupValue,ite_eq_right hij]
      exact ih hn.2 h

lemma constantTable_lookup {α : Type} (e : Encoding α) (f : α → ℕ) (a : α) :
    AExpr.lookupValue ((e.code a).val) (constantTable e f)=f a := by
  apply lookupValue_mem
  · simp only [constantTable,List.map_map,Function.comp_def]
    exact List.Nodup.map (fun x y h=>e.code.injective (Fin.ext h)) e.nodup_enumerate
  · exact List.mem_map.mpr ⟨a,e.mem_enumerate a,rfl⟩

lemma constantTable_eval {α : Type} (e : Encoding α) (f : α → ℕ) (a : α)
    (x : AExpr) (v : List ℕ) (hx : x.eval v=(e.code a).val) :
    (x.lookup (constantTable e f)).eval v=f a := by
  rw [AExpr.eval_lookup,hx,constantTable_lookup]

end MinUncut.Outer.LocalTemplate

end
end

end OAI
