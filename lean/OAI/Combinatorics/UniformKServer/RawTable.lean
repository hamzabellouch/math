import Mathlib
import OAI.Combinatorics.UniformKServer.PrimitiveRules
import OAI.Combinatorics.UniformKServer.RawWords

namespace OAI

                               
section

namespace UniformKServer.RawTable
open RawArithmetic RawWords

def history (w g : List ℕ) : List (ℕ×ℕ) :=
  (List.range w.length).map fun i=>(w.getD i 0,g.getD i 0)
def key (p c : List ℕ) (r j : ℕ) : ℕ := Encodable.encode (p,c,r,j)
def entry (T : List ℕ) (p c : List ℕ) (r j : ℕ) : ℕ := T.getD (key p c r j) 0
def dist (n : ℕ) (d : List Q) (x y : ℕ) : Q := d.getD (x*n+y) (natural 0)
abbrev PathState := (List ℕ × List ℕ) × (ℕ × Q)
def pathStep (n : ℕ) (d : List Q) (T : List ℕ) (z : PathState) (rj : ℕ×ℕ) : PathState :=
  ((z.1.1++[rj.1], z.1.2.set rj.2 rj.1),
    (z.2.1*entry T z.1.1 z.1.2 rj.1 rj.2,
      add z.2.2 (dist n d (z.1.2.getD rj.2 0) rj.1)))
def path (n : ℕ) (d : List Q) (T : List ℕ) (p c w g : List ℕ) : PathState :=
  (history w g).foldl (pathStep n d T) ((p,c),(1,natural 0))
def term (n : ℕ) (d : List Q) (T : List ℕ) (p c w g : List ℕ) : Q :=
  let z:=path n d T p c w g
  mul (natural z.2.1) z.2.2

def total (n k : ℕ) (d : List Q) (T : List ℕ) (p c w : List ℕ) : Q :=
  ((words k w.length).map fun g=>term n d T p c w g).foldr add (natural 0)
def expected (n k b : ℕ) (d : List Q) (T : List ℕ) (p c w : List ℕ) : Q :=
  divide (total n k d T p c w) (2^(b*w.length)-1)
def cost (n : ℕ) (d : List Q) (c w g : List ℕ) : Q := (path n d [] [] c w g).2.2

section Primitive
open Primrec
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_natural (f : α→ℕ) (hf : Primrec f) :
    Primrec (fun x=>natural (f x)) := RawArithmetic.primitive_natural.comp hf
@[fun_prop] theorem primitive_add (f g : α→Q) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>add (f x) (g x)) := RawArithmetic.primitive_add.comp hf hg
@[fun_prop] theorem primitive_mul (f g : α→Q) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>mul (f x) (g x)) := RawArithmetic.primitive_mul.comp hf hg
@[fun_prop] theorem primitive_divide (f : α→Q) (g : α→ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>divide (f x) (g x)) := RawArithmetic.primitive_divide.comp hf hg
@[fun_prop] theorem primitive_words (f g : α→ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>words (f x) (g x)) := RawWords.primitive_words.comp hf hg
@[fun_prop] theorem primitive_upto (f g : α→ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>upto (f x) (g x)) := RawWords.primitive_upto.comp hf hg
@[fun_prop] theorem primitive_sum (f : α→List ℕ) (hf : Primrec f) :
    Primrec (fun x=>(f x).sum) := RawWords.primitive_sum.comp hf

@[fun_prop] theorem primitive_history (f g : α→List ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>history (f x) (g x)) := by unfold history;fun_prop
@[fun_prop] theorem primitive_key (p c : α→List ℕ) (r j : α→ℕ)
    (hp : Primrec p) (hc : Primrec c) (hr : Primrec r) (hj : Primrec j) :
    Primrec (fun x=>key (p x) (c x) (r x) (j x)) := by unfold key;fun_prop
@[fun_prop] theorem primitive_entry (T p c : α→List ℕ) (r j : α→ℕ)
    (hT : Primrec T) (hp : Primrec p) (hc : Primrec c) (hr : Primrec r) (hj : Primrec j) :
    Primrec (fun x=>entry (T x) (p x) (c x) (r x) (j x)) := by unfold entry;fun_prop
@[fun_prop] theorem primitive_dist (n : α→ℕ) (d : α→List Q) (x y : α→ℕ)
    (hn : Primrec n) (hd : Primrec d) (hx : Primrec x) (hy : Primrec y) :
    Primrec (fun v=>dist (n v) (d v) (x v) (y v)) := by unfold dist;fun_prop
@[fun_prop] theorem primitive_pathStep (n : α→ℕ) (d : α→List Q) (T : α→List ℕ)
    (z : α→PathState) (rj : α→ℕ×ℕ) (hn : Primrec n) (hd : Primrec d)
    (hT : Primrec T) (hz : Primrec z) (hrj : Primrec rj) :
    Primrec (fun x=>pathStep (n x) (d x) (T x) (z x) (rj x)) := by unfold pathStep;fun_prop
@[fun_prop] theorem primitive_path (n : α→ℕ) (d : α→List Q) (T p c w g : α→List ℕ)
    (hn : Primrec n) (hd : Primrec d) (hT : Primrec T) (hp : Primrec p)
    (hc : Primrec c) (hw : Primrec w) (hg : Primrec g) :
    Primrec (fun x=>path (n x) (d x) (T x) (p x) (c x) (w x) (g x)) := by
  unfold path
  apply Primrec.list_foldl (h:=fun x v=>pathStep (n x) (d x) (T x) v.1 v.2)
  · fun_prop
  · fun_prop
  · change Primrec (fun a : α × (PathState × (ℕ×ℕ)) =>
      pathStep (n a.1) (d a.1) (T a.1) a.2.1 a.2.2)
    fun_prop
@[fun_prop] theorem primitive_term (n : α→ℕ) (d : α→List Q) (T p c w g : α→List ℕ)
    (hn : Primrec n) (hd : Primrec d) (hT : Primrec T) (hp : Primrec p)
    (hc : Primrec c) (hw : Primrec w) (hg : Primrec g) :
    Primrec (fun x=>term (n x) (d x) (T x) (p x) (c x) (w x) (g x)) := by
  unfold term
  fun_prop
@[fun_prop] theorem primitive_total (n k : α→ℕ) (d : α→List Q) (T p c w : α→List ℕ)
    (hn : Primrec n) (hk : Primrec k) (hd : Primrec d) (hT : Primrec T) (hp : Primrec p)
    (hc : Primrec c) (hw : Primrec w) :
    Primrec (fun x=>total (n x) (k x) (d x) (T x) (p x) (c x) (w x)) := by
  unfold total
  apply RawWords.primitive_Qsum.comp
  fun_prop
@[fun_prop] theorem primitive_expected (n k b : α→ℕ) (d : α→List Q) (T p c w : α→List ℕ)
    (hn : Primrec n) (hk : Primrec k) (hb : Primrec b) (hd : Primrec d) (hT : Primrec T)
    (hp : Primrec p) (hc : Primrec c) (hw : Primrec w) :
    Primrec (fun x=>expected (n x) (k x) (b x) (d x) (T x) (p x) (c x) (w x)) := by
  unfold expected
  fun_prop
@[fun_prop] theorem primitive_cost (n : α→ℕ) (d : α→List Q) (c w g : α→List ℕ)
    (hn : Primrec n) (hd : Primrec d) (hc : Primrec c) (hw : Primrec w) (hg : Primrec g) :
    Primrec (fun x=>cost (n x) (d x) (c x) (w x) (g x)) := by unfold cost;fun_prop
end Primitive
end UniformKServer.RawTable

end


end OAI
