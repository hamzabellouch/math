import Mathlib
import OAI.Combinatorics.UniformKServer.RawTable

namespace OAI

                                     
section

/-! Finite arithmetic certificates of the *unknown-offset* construction.
The verifier checks every finite word and every hindsight label history; no
competitive conclusion is an input. All its checks are primitive recursive. -/
namespace UniformKServer.RawCertificate
open RawArithmetic RawWords RawTable

abbrev Input := ℕ × ℕ × List Q
abbrev Certificate := (ℕ × ℕ × ℕ × ℕ) × (Q × Q) × List ℕ

def ell (v : Certificate) := v.1.1
def bits (v : Certificate) := v.1.2.1
def cap (v : Certificate) := v.1.2.2.1
def restart (v : Certificate) := v.1.2.2.2
def diam (v : Certificate) := v.2.1.1
def sep (v : Certificate) := v.2.1.2
def table (v : Certificate) := v.2.2

def horizon (k M : ℕ) := ((List.range (M+1)).map fun i=>k^i).sum

def rowOK (k b : ℕ) (T p c : List ℕ) (r : ℕ) : Bool :=
  decide (((List.range k).map fun j=>entry T p c r j).sum=2^b) &&
  (List.range k).all fun j=>
    (!(c.any fun x=>decide (x=r))) || decide (c.getD j 0=r) || decide (entry T p c r j=0)

def rowsOK (n k H b : ℕ) (T : List ℕ) : Bool :=
  (upto n H).all fun p=>(words n k).all fun c=>(List.range n).all fun r=>rowOK k b T p c r

def tableOK (n k H b A R : ℕ) (d : List Q) (D δ : Q) (T : List ℕ) : Bool :=
  (upto n H).all fun w=>(words k w.length).all fun g=> decide
    (le (expected n k b d T [] (List.range k) w)
      (add (mul (natural A) (cost n d (List.range k) w g)) (add (mul (natural R) δ) D)))

def numbersOK (k : ℕ) (v : Certificate) : Bool :=
  decide (0<ell v) && decide (2^(ell v-1)<k+1) && decide (k+1≤2^(ell v)) &&
  decide (0<restart v) && decide (0<(sep v).1) &&
  decide (le (mul (natural k) (diam v)) (mul (natural (restart v)) (sep v))) &&
  decide (le (mul (natural (restart v*(k+1))) (diam v)) (mul (natural (cap v+1)) (sep v)))

def boundsOK (n : ℕ) (d : List Q) (D δ : Q) : Bool :=
  (List.range n).all (fun x=>(List.range n).all fun y=>
    decide (le (dist n d x y) D) && (decide (x=y) || decide (le δ (dist n d x y))))

def verify (mult : ℕ) (i : Input) (v : Certificate) : Bool :=
  let n:=i.1; let k:=i.2.1; let d:=i.2.2
  let H:=horizon k (cap v)
  numbersOK k v && boundsOK n d (diam v) (sep v) &&
  rowsOK n k H (bits v) (table v) &&
  tableOK n k H (bits v) (mult*(ell v)^2) (restart v) d (diam v) (sep v) (table v)

section Primitive
open Primrec
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_le (f g : α→Q) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>decide (le (f x) (g x))) := (RawArithmetic.primitive_le.comp hf hg).decide
@[fun_prop] theorem primitive_any (f : α→List ℕ) (g : α→ℕ→Bool) (hf : Primrec f)
    (hg : Primrec (fun p : α×ℕ=>g p.1 p.2)) :
    Primrec (fun x=>(f x).any (g x)) := by
  have h : Primrec (fun x=> !((f x).all fun y=> !(g x y))) := by fun_prop
  exact h.of_eq (by intro x;simp [List.any_eq_not_all_not])
@[fun_prop] theorem primitive_horizon (k M : α→ℕ) (hk : Primrec k) (hM : Primrec M) :
    Primrec (fun x=>horizon (k x) (M x)) := by unfold horizon;fun_prop
@[fun_prop] theorem primitive_rowOK (k b : α→ℕ) (T p c : α→List ℕ) (r : α→ℕ)
    (hk : Primrec k) (hb : Primrec b) (hT : Primrec T) (hp : Primrec p) (hc : Primrec c) (hr : Primrec r) :
    Primrec (fun x=>rowOK (k x) (b x) (T x) (p x) (c x) (r x)) := by unfold rowOK;fun_prop
@[fun_prop] theorem primitive_rowsOK (n k H b : α→ℕ) (T : α→List ℕ)
    (hn : Primrec n) (hk : Primrec k) (hH : Primrec H) (hb : Primrec b) (hT : Primrec T) :
    Primrec (fun x=>rowsOK (n x) (k x) (H x) (b x) (T x)) := by unfold rowsOK;fun_prop
@[fun_prop] theorem primitive_tableOK (n k H b A R : α→ℕ) (d : α→List Q) (D δ : α→Q) (T : α→List ℕ)
    (hn : Primrec n) (hk : Primrec k) (hH : Primrec H) (hb : Primrec b) (hA : Primrec A)
    (hR : Primrec R) (hd : Primrec d) (hD : Primrec D) (hδ : Primrec δ) (hT : Primrec T) :
    Primrec (fun x=>tableOK (n x) (k x) (H x) (b x) (A x) (R x) (d x) (D x) (δ x) (T x)) := by
  unfold tableOK;fun_prop

@[fun_prop] theorem primitive_numbersOK (k : α→ℕ) (v : α→Certificate)
    (hk : Primrec k) (hv : Primrec v) : Primrec (fun x=>numbersOK (k x) (v x)) := by
  unfold numbersOK ell cap restart diam sep
  fun_prop
@[fun_prop] theorem primitive_boundsOK (n : α→ℕ) (d : α→List Q) (D δ : α→Q)
    (hn : Primrec n) (hd : Primrec d) (hD : Primrec D) (hδ : Primrec δ) :
    Primrec (fun x=>boundsOK (n x) (d x) (D x) (δ x)) := by unfold boundsOK;fun_prop

theorem primitive_verify (mult : ℕ) : Primrec₂ (verify mult) := by
  unfold verify ell bits cap restart diam sep table
  change Primrec (fun p : Input×Certificate=> _)
  fun_prop
end Primitive
end UniformKServer.RawCertificate

end



end OAI
