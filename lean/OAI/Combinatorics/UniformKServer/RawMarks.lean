import Mathlib
import OAI.Combinatorics.UniformKServer.PrimitiveRules
import OAI.Combinatorics.UniformKServer.Fallback
import OAI.Combinatorics.UniformKServer.RawTyped

namespace OAI

noncomputable section
                               
section

namespace UniformKServer.RawMarks
open RawTyped

def bits {a : ℕ} (A : Finset (Fin a)) : List Bool := List.ofFn fun j=>decide (j∈A)
def empty (a : ℕ) : List Bool := List.replicate a false
def insert (A : List Bool) (j : ℕ) : List Bool := A.set j true
def card (A : List Bool) : ℕ := (A.map (fun b=>if b then 1 else 0)).sum
def complement (A : List Bool) : List Bool := A.map Bool.not
def covers (c : List ℕ) (r : ℕ) : List Bool := c.map (fun x=>decide (x=r))
def pick (A : List Bool) : ℕ := let j:=A.findIdx id; if j<A.length then j else 0

theorem length_bits {a : ℕ} (A : Finset (Fin a)) : (bits A).length=a := by simp [bits]
@[simp] theorem empty_bits (a : ℕ) : empty a=bits (∅ : Finset (Fin a)) := by
  simp [empty,bits,List.ofFn_const]
@[simp] theorem insert_bits {a : ℕ} (A : Finset (Fin a)) (j : Fin a) :
    insert (bits A) j.val=bits (Insert.insert j A) := by
  apply List.ext_getElem
  · simp [insert,bits]
  · intro i hi hj
    simp only [insert,List.length_set,List.length_ofFn,bits] at hi hj ⊢
    rw [List.getElem_set]
    simp only [List.getElem_ofFn,Finset.mem_insert]
    by_cases h : j.val=i
    · have he : (⟨i,hj⟩ : Fin a)=j := Fin.ext h.symm
      simp [h,he]
    · have he : (⟨i,hj⟩ : Fin a)≠j := by intro he;exact h (congrArg Fin.val he).symm
      simp [h,he]
@[simp] theorem card_bits {a : ℕ} (A : Finset (Fin a)) : card (bits A)=A.card := by
  simp [card,bits,List.map_ofFn,List.sum_ofFn]
@[simp] theorem complement_bits {a : ℕ} (A : Finset (Fin a)) :
    complement (bits A)=bits (Finset.univ\A) := by
  simp [complement,bits,List.map_ofFn,Function.comp_def]
@[simp] theorem covers_bits {n k : ℕ} (c : Configuration n k) (r : Fin n) :
    covers (config c) r.val=bits (Fallback.coverers c r) := by
  simp [covers,config,bits,Fallback.coverers,List.map_ofFn,Fin.ext_iff,Function.comp_def]

@[simp] theorem pick_bits {a : ℕ} (ha : 0<a) (A : Finset (Fin a)) :
    pick (bits A)=(Fallback.pick ha A).val := by
  by_cases h : A.Nonempty
  · let j:=A.min' h
    have hj : j.val<(bits A).length := by simp [length_bits]
    have hf : (bits A).findIdx id=j.val := by
      apply (List.findIdx_eq hj).mpr
      constructor
      · simpa [bits] using Finset.min'_mem A h
      · intro i hi
        simp only [bits,List.getElem_ofFn,id_eq,decide_eq_false_iff_not]
        intro hm
        have hh:=Finset.min'_le A (⟨i,lt_trans hi j.isLt⟩ : Fin a) hm
        exact (Nat.not_le_of_lt hi) hh
    simp only [pick,hf,ite_eq_left hj,Fallback.pick,dite_eq_left h,j]
  · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst A
    have hf : (bits (∅ : Finset (Fin a))).findIdx id=a := by
      calc
        _ = (bits (∅ : Finset (Fin a))).length := List.findIdx_eq_length_of_false (by
          intro b hb
          simp [bits] at hb
          simp [hb])
        _ = a := length_bits _
    simp [pick,hf,length_bits,Fallback.pick]

section Primitive
open Primrec
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_empty (f : α→ℕ) (hf : Primrec f) :
    Primrec (fun x=>empty (f x)) := by
  have h : Primrec (fun x=>(List.range (f x)).map (fun _=>false)) := by fun_prop
  exact h.of_eq (by intro x;simp [empty])
@[fun_prop] theorem primitive_insert (f : α→List Bool) (j : α→ℕ) (hf : Primrec f) (hj : Primrec j) :
    Primrec (fun x=>insert (f x) (j x)) := by unfold insert;fun_prop
@[fun_prop] theorem primitive_card (f : α→List Bool) (hf : Primrec f) :
    Primrec (fun x=>card (f x)) := by
  unfold card
  apply RawTable.primitive_sum
  apply PrimitiveRules.map _ _ hf
  exact (Primrec.dom_finite (f:=fun b : Bool=>if b then 1 else 0)).comp Primrec.snd
@[fun_prop] theorem primitive_complement (f : α→List Bool) (hf : Primrec f) :
    Primrec (fun x=>complement (f x)) := by unfold complement;fun_prop
@[fun_prop] theorem primitive_covers (f : α→List ℕ) (r : α→ℕ) (hf : Primrec f) (hr : Primrec r) :
    Primrec (fun x=>covers (f x) (r x)) := by unfold covers;fun_prop
@[fun_prop] theorem primitive_pick (f : α→List Bool) (hf : Primrec f) :
    Primrec (fun x=>pick (f x)) := by
  have hg : Primrec (fun x=>(f x).findIdx id) := Primrec.list_findIdx hf Primrec.snd
  unfold pick
  exact Primrec.ite (Primrec.nat_lt.comp hg (Primrec.list_length.comp hf)) hg (Primrec.const 0)
end Primitive
end UniformKServer.RawMarks

end


end

end OAI
