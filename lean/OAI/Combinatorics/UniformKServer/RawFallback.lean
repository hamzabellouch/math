import Mathlib
import OAI.Combinatorics.UniformKServer.EpochShadow
import OAI.Combinatorics.UniformKServer.RawMarks

namespace OAI

noncomputable section
                                  
section

namespace UniformKServer.RawFallback
open RawTyped RawMarks

def endpoint (k : ℕ) (seen : List Bool) (r : ℕ) : Bool :=
  decide (k<card (RawMarks.insert seen r))
def choose (c : List ℕ) (marked : List Bool) (r : ℕ) : ℕ :=
  bif decide (0<card (covers c r)) then pick (covers c r) else pick (complement marked)
def label (k : ℕ) (c : List ℕ) (marked seen : List Bool) (r : ℕ) : ℕ :=
  bif endpoint k seen r then pick (covers c r) else choose c marked r
def nextMarked (k : ℕ) (marked seen : List Bool) (r j : ℕ) : List Bool :=
  bif endpoint k seen r then empty k else RawMarks.insert marked j
def nextSeen (n k : ℕ) (seen : List Bool) (r : ℕ) : List Bool :=
  bif endpoint k seen r then empty n else RawMarks.insert seen r

@[simp] theorem endpoint_bits {n k : ℕ} (s : Finset (Fin n)) (r : Fin n) :
    endpoint k (bits s) r.val=decide (k<(Insert.insert r s).card) := by
  simp only [endpoint,insert_bits,card_bits]

@[simp] theorem choose_bits {n k : ℕ} (hk : 0<k) (c : Configuration n k)
    (A : Finset (Fin k)) (r : Fin n) :
    choose (config c) (bits A) r.val=(Fallback.choose hk ⟨c,A⟩ r).val := by
  simp only [choose,covers_bits,card_bits,Finset.card_pos,Bool.cond_decide,
    complement_bits,pick_bits hk,Fallback.choose]
  split_ifs <;> simp_all

@[simp] theorem label_bits {n k : ℕ} (hk : 0<k) (s : Fallback.RawState n k) (r : Fin n) :
    label k (config s.marking.position) (bits s.marking.marked) (bits s.seen) r.val=
      (Fallback.rawChoice hk s r).val := by
  by_cases he : Fallback.isEndpoint s r
  · have he' : k<(Insert.insert r s.seen).card := he
    simp only [label,endpoint_bits,Bool.cond_decide,ite_eq_left he',covers_bits,pick_bits hk,
      Fallback.rawChoice,ite_eq_left he]
  · have he' : ¬k<(Insert.insert r s.seen).card := he
    simp only [label,endpoint_bits,Bool.cond_decide,ite_eq_right he',choose_bits hk,
      Fallback.rawChoice,ite_eq_right he]

@[simp] theorem nextSeen_bits {n k : ℕ} (s : Finset (Fin n)) (r : Fin n) :
    nextSeen n k (bits s) r.val=bits (EpochShadow.bookStep (k:=k) s r) := by
  simp only [nextSeen,endpoint_bits,Bool.cond_decide,empty_bits,insert_bits,EpochShadow.bookStep]
  split_ifs <;> simp_all

theorem step_bits {n k : ℕ} (hk : 0<k) (s : Fallback.RawState n k) (r : Fin n) :
    let j:=label k (config s.marking.position) (bits s.marking.marked) (bits s.seen) r.val
    ((config s.marking.position).set j r.val,
      nextMarked k (bits s.marking.marked) (bits s.seen) r.val j,
      nextSeen n k (bits s.seen) r.val)=
    (config (Fallback.rawStep hk s r).marking.position,
      bits (Fallback.rawStep hk s r).marking.marked,bits (Fallback.rawStep hk s r).seen) := by
  dsimp only
  rw [label_bits hk,config_set]
  by_cases he : Fallback.isEndpoint s r
  · have he' : k<(Insert.insert r s.seen).card := he
    simp only [nextMarked,nextSeen,endpoint_bits,Bool.cond_decide,ite_eq_left he',
      Fallback.rawStep,ite_eq_left he,empty_bits]
  · have he' : ¬k<(Insert.insert r s.seen).card := he
    simp only [nextMarked,nextSeen,endpoint_bits,Bool.cond_decide,ite_eq_right he',
      Fallback.rawStep,ite_eq_right he,Fallback.rawChoice,Fallback.step,insert_bits]

section Primitive
open Primrec
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_endpoint (k : α→ℕ) (s : α→List Bool) (r : α→ℕ)
    (hk : Primrec k) (hs : Primrec s) (hr : Primrec r) :
    Primrec (fun x=>endpoint (k x) (s x) (r x)) := by unfold endpoint;fun_prop
@[fun_prop] theorem primitive_choose (c : α→List ℕ) (m : α→List Bool) (r : α→ℕ)
    (hc : Primrec c) (hm : Primrec m) (hr : Primrec r) :
    Primrec (fun x=>choose (c x) (m x) (r x)) := by
  unfold choose
  exact Primrec.cond (by fun_prop) (by fun_prop) (by fun_prop)
@[fun_prop] theorem primitive_label (k : α→ℕ) (c : α→List ℕ) (m s : α→List Bool) (r : α→ℕ)
    (hk : Primrec k) (hc : Primrec c) (hm : Primrec m) (hs : Primrec s) (hr : Primrec r) :
    Primrec (fun x=>label (k x) (c x) (m x) (s x) (r x)) := by
  unfold label
  exact Primrec.cond (by fun_prop) (by fun_prop) (by fun_prop)
@[fun_prop] theorem primitive_nextMarked (k : α→ℕ) (m s : α→List Bool) (r j : α→ℕ)
    (hk : Primrec k) (hm : Primrec m) (hs : Primrec s) (hr : Primrec r) (hj : Primrec j) :
    Primrec (fun x=>nextMarked (k x) (m x) (s x) (r x) (j x)) := by
  unfold nextMarked
  exact Primrec.cond (by fun_prop) (by fun_prop) (by fun_prop)
@[fun_prop] theorem primitive_nextSeen (n k : α→ℕ) (s : α→List Bool) (r : α→ℕ)
    (hn : Primrec n) (hk : Primrec k) (hs : Primrec s) (hr : Primrec r) :
    Primrec (fun x=>nextSeen (n x) (k x) (s x) (r x)) := by
  unfold nextSeen
  exact Primrec.cond (by fun_prop) (by fun_prop) (by fun_prop)
end Primitive
end UniformKServer.RawFallback

end


end

end OAI
