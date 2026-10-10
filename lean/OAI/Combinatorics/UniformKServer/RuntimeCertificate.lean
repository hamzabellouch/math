import Mathlib
import OAI.Combinatorics.UniformKServer.RawFinite
import OAI.Combinatorics.UniformKServer.LiteralBound

namespace OAI

noncomputable section

namespace UniformKServer.RuntimeCertificate
open RawProgram RawCertificate RawFinite Primrec
open scoped Classical
abbrev Cert := List ℕ×ℕ

def has (S : List ℕ) (u : ℕ) : Bool := S.any (fun x=>decide (x=u))
def B (k : ℕ) (v : Certificate) : ℕ := RawCertificate.horizon k (cap v)*bits v

def item (k : ℕ) (S : List ℕ) (T u r a : ℕ) : Bool :=
  decide (chosen (unpack u) (requestToken r) a<k) &&
  has S (Encodable.encode (next (unpack u) (requestToken r) a)) &&
  decide ((chosen (unpack u) (requestToken r) a).bits.length≤T) &&
  LiteralBound.finishes T u (requestToken r) a

def row (k b : ℕ) (S : List ℕ) (T u r : ℕ) : Bool :=
  decide ((natCode (r+1)).length+1≤T) &&
    (List.range (2^(b+1))).all (fun a=>item k S T u r a)

def node (n k b : ℕ) (S : List ℕ) (T u : ℕ) : Bool :=
  decide (u.bits.length+1≤T) && (List.range n).all (fun r=>row k b S T u r)

def verify (n k : ℕ) (v : Certificate) (c : Cert) : Bool :=
  has c.1 (Encodable.encode (RawProgram.initial n k v)) && decide (B k v+1≤c.2) &&
  c.1.all (fun u=>node n k (B k v) c.1 c.2 u)

section Primitive
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_has (S : α→List ℕ) (u : α→ℕ) (hS : Primrec S) (hu : Primrec u) :
    Primrec (fun x=>has (S x) (u x)) := by unfold has;fun_prop
@[fun_prop] theorem primitive_B (k : α→ℕ) (v : α→Certificate) (hk : Primrec k) (hv : Primrec v) :
    Primrec (fun x=>B (k x) (v x)) := by unfold B cap bits;fun_prop
@[fun_prop] theorem primitive_requestToken (r : α→ℕ) (hr : Primrec r) :
    Primrec (fun x=>requestToken (r x)) := by unfold requestToken;fun_prop
@[fun_prop] theorem primitive_initial (n k : α→ℕ) (v : α→Certificate)
    (hn : Primrec n) (hk : Primrec k) (hv : Primrec v) :
    Primrec (fun x=>RawProgram.initial (n x) (k x) (v x)) := by unfold RawProgram.initial payload;fun_prop
@[fun_prop] theorem primitive_finishes (t u r a : α→ℕ)
    (ht : Primrec t) (hu : Primrec u) (hr : Primrec r) (ha : Primrec a) :
    Primrec (fun x=>LiteralBound.finishes (t x) (u x) (r x) (a x)) :=
  LiteralBound.primitive_finishes.comp (ht.pair (hu.pair (hr.pair ha)))
@[fun_prop] theorem primitive_item (k : α→ℕ) (S : α→List ℕ) (T u r a : α→ℕ)
    (hk : Primrec k) (hS : Primrec S) (hT : Primrec T) (hu : Primrec u) (hr : Primrec r) (ha : Primrec a) :
    Primrec (fun x=>item (k x) (S x) (T x) (u x) (r x) (a x)) := by
  have hp:=RawProgram.primitive_unpack u hu
  have hq:=primitive_requestToken r hr
  have hc:=RawProgram.primitive_chosen _ _ _ hp hq ha
  have hn:=RawProgram.primitive_next _ _ _ hp hq ha
  unfold item
  apply PrimitiveRules.bool_and
  · apply PrimitiveRules.bool_and
    · apply PrimitiveRules.bool_and
      · exact PrimitiveRules.lts _ _ hc hk
      · exact primitive_has _ _ hS (Primrec.encode.comp hn)
    · exact PrimitiveRules.les _ _ (Primrec.list_length.comp (RawBits.primitive_bits.comp hc)) hT
  · exact primitive_finishes _ _ _ _ hT hu hq ha
@[fun_prop] theorem primitive_row (k b : α→ℕ) (S : α→List ℕ) (T u r : α→ℕ)
    (hk : Primrec k) (hb : Primrec b) (hS : Primrec S) (hT : Primrec T) (hu : Primrec u) (hr : Primrec r) :
    Primrec (fun x=>row (k x) (b x) (S x) (T x) (u x) (r x)) := by unfold row;fun_prop
@[fun_prop] theorem primitive_node (n k b : α→ℕ) (S : α→List ℕ) (T u : α→ℕ)
    (hn : Primrec n) (hk : Primrec k) (hb : Primrec b) (hS : Primrec S) (hT : Primrec T) (hu : Primrec u) :
    Primrec (fun x=>node (n x) (k x) (b x) (S x) (T x) (u x)) := by unfold node;fun_prop
 theorem primitive_verify : Primrec (fun p : (ℕ×ℕ×Certificate)×Cert=>verify p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  unfold verify
  apply PrimitiveRules.bool_and
  · apply PrimitiveRules.bool_and
    · apply primitive_has
      · exact Primrec.fst.comp Primrec.snd
      · exact Primrec.encode.comp (primitive_initial _ _ _ (by fun_prop) (by fun_prop) (by fun_prop))
    · exact PrimitiveRules.les _ _
        (Primrec.succ.comp (primitive_B _ _ (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))) (Primrec.snd.comp Primrec.snd)
  · apply PrimitiveRules.bool_all
    · exact Primrec.fst.comp Primrec.snd
    · exact primitive_node _ _ _ _ _ _
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
        (primitive_B _ _ (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
end Primitive

@[simp] theorem has_iff (S : List ℕ) (u : ℕ) : has S u=true ↔ u∈S := by
  simp [has,List.any_eq_true]

 theorem verify_iff (n k : ℕ) (v : Certificate) (c : Cert) :
    verify n k v c=true ↔
      Encodable.encode (RawProgram.initial n k v)∈c.1 ∧ B k v+1≤c.2 ∧
      ∀u∈c.1,u.bits.length+1≤c.2 ∧ ∀r<n,(natCode (r+1)).length+1≤c.2 ∧
        ∀a<2^(B k v+1),chosen (unpack u) (requestToken r) a<k ∧
          Encodable.encode (next (unpack u) (requestToken r) a)∈c.1 ∧
          (chosen (unpack u) (requestToken r) a).bits.length≤c.2 ∧
          LiteralBound.finishes c.2 u (requestToken r) a=true := by
  simp only [verify,node,row,item,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,
    List.mem_range,has_iff,and_assoc]

end UniformKServer.RuntimeCertificate

end

end OAI
