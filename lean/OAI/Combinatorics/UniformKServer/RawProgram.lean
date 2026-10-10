import Mathlib
import OAI.Combinatorics.UniformKServer.RawGlobal
import OAI.Combinatorics.UniformKServer.RawBits

namespace OAI

noncomputable section
                                 
section

namespace UniformKServer.RawProgram
open Primrec RawCertificate
attribute [fun_prop] RawBits.primitive_bits

abbrev Payload := ℕ×ℕ×Certificate×RawGlobal.S

def payload (n k : ℕ) (v : Certificate) (s : RawGlobal.S) : Payload := (n,k,v,s)
def initial (n k : ℕ) (v : Certificate) : Payload := payload n k v (RawGlobal.initial n k)
def unpack (a : ℕ) : Payload := (Encodable.decode a).getD default

def request (a : ℕ) : ℕ := (RawBinary.readNat a.bits).1-1

def fresh (k M b a : ℕ) : List ℕ :=
  (List.range (RawCertificate.horizon k M)).map (fun i=>RawBinary.value ((a.bits.drop (b*i)).take b))

def chosen (p : Payload) (r a : ℕ) : ℕ :=
  RawGlobal.label p.2.1 (table p.2.2.1) p.2.2.2 (request r)
    (fresh p.2.1 (cap p.2.2.1) (bits p.2.2.1) a)

def next (p : Payload) (r a : ℕ) : Payload :=
  payload p.1 p.2.1 p.2.2.1
    (RawGlobal.step p.1 p.2.1 (cap p.2.2.1) (restart p.2.2.1) (table p.2.2.1)
      p.2.2.2 (request r) (fresh p.2.1 (cap p.2.2.1) (bits p.2.2.1) a))

def randomCount (p : Payload) : ℕ := RawCertificate.horizon p.2.1 (cap p.2.2.1)*bits p.2.2.1

def run (v : List.Vector ℕ 3) : List.Vector ℕ 3 :=
  let p:=unpack (v.get 0)
  ⟨[chosen p (v.get 1) (v.get 2),2^randomCount p,
      Encodable.encode (next p (v.get 1) (v.get 2))],rfl⟩

section Primitive
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_natCode (a : α→ℕ) (ha : Primrec a) :
    Primrec (fun x=>natCode (a x)) := by
  unfold natCode
  have hb:=RawBits.primitive_bits.comp ha
  have hr : Primrec (fun x=>List.replicate (a x).bits.length true) := by
    have h := Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp hb))
      (Primrec.const true : Primrec (fun _ : α×ℕ=>true)).to₂
    exact h.of_eq (by intro x;simp)
  exact Primrec.list_append.comp
    (Primrec.list_append.comp hr
      (Primrec.const [false])) hb
@[fun_prop] theorem primitive_unpack (a : α→ℕ) (ha : Primrec a) :
    Primrec (fun x=>unpack (a x)) :=
  Primrec.option_getD.comp (Primrec.decode.comp ha) (Primrec.const default)
@[fun_prop] theorem primitive_request (a : α→ℕ) (ha : Primrec a) :
    Primrec (fun x=>request (a x)) := by unfold request;fun_prop
@[fun_prop] theorem primitive_fresh (k M b a : α→ℕ) (hk : Primrec k) (hM : Primrec M)
    (hb : Primrec b) (ha : Primrec a) : Primrec (fun x=>fresh (k x) (M x) (b x) (a x)) := by
  unfold fresh
  have hm : Primrec (fun p : α×ℕ=>RawBinary.value (((a p.1).bits.drop (b p.1*p.2)).take (b p.1))) :=
    RawBinary.primitive_value _ (Primrec.list_take.comp (by fun_prop)
      (Primrec.list_drop.comp (by fun_prop) (by fun_prop)))
  exact Primrec.list_map (by fun_prop) hm.to₂
@[fun_prop] theorem primitive_chosen (p : α→Payload) (r a : α→ℕ)
    (hp : Primrec p) (hr : Primrec r) (ha : Primrec a) :
    Primrec (fun x=>chosen (p x) (r x) (a x)) := by unfold chosen table cap bits;fun_prop
@[fun_prop] theorem primitive_next (p : α→Payload) (r a : α→ℕ)
    (hp : Primrec p) (hr : Primrec r) (ha : Primrec a) :
    Primrec (fun x=>next (p x) (r x) (a x)) := by unfold next payload table cap restart bits;fun_prop
@[fun_prop] theorem primitive_randomCount (p : α→Payload) (hp : Primrec p) :
    Primrec (fun x=>randomCount (p x)) := by unfold randomCount cap bits;fun_prop
@[fun_prop] theorem primitive_get {n : ℕ} (v : α→List.Vector ℕ n) (i : Fin n) (hv : Primrec v) :
    Primrec (fun x=>(v x).get i) := Primrec.vector_get.comp hv (Primrec.const i)
 theorem primitive_run : Primrec run := by
  apply Primrec.vector_toList_iff.mp
  change Primrec (fun v : List.Vector ℕ 3=>
    [chosen (unpack (v.get 0)) (v.get 1) (v.get 2),2^randomCount (unpack (v.get 0)),
      Encodable.encode (next (unpack (v.get 0)) (v.get 1) (v.get 2))])
  fun_prop
end Primitive

@[simp] theorem unpack_encode (p : Payload) : unpack (Encodable.encode p)=p := by
  simp [unpack]
@[simp] theorem request_code (r : ℕ) :
    request (RawBinary.value (natCode (r+1)++[true]))=r := by
  simp only [request,RawBits.bits_value,RawBinary.read_natCode,Nat.add_sub_cancel]

end UniformKServer.RawProgram

end


end

end OAI
