import Mathlib

namespace OAI

                                     
section

/-! Composition rules for the explicit primitive-recursive constructor.
`fun_prop` only builds terms from the listed proved closure lemmas. -/
attribute [fun_prop] Primrec
attribute [fun_prop] Primrec.id Primrec.const Primrec.comp Primrec.pair Primrec.fst Primrec.snd

namespace UniformKServer.PrimitiveRules
open Primrec
variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]

@[fun_prop] theorem add (f g : α→ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>f x+g x) := nat_add.comp hf hg
@[fun_prop] theorem mul (f g : α→ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>f x*g x) := nat_mul.comp hf hg
@[fun_prop] theorem sub (f g : α→ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>f x-g x) := nat_sub.comp hf hg
@[fun_prop] theorem pow (f g : α→ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>f x^g x) := (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp hf hg
@[fun_prop] theorem div (f g : α→ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>f x/g x) := nat_div.comp hf hg
@[fun_prop] theorem eqs [DecidableEq β] (f g : α→β) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>decide (f x=g x)) := (Primrec.eq.comp hf hg).decide
@[fun_prop] theorem les (f g : α→ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>decide (f x≤g x)) := (nat_le.comp hf hg).decide
@[fun_prop] theorem lts (f g : α→ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>decide (f x<g x)) := (nat_lt.comp hf hg).decide
@[fun_prop] theorem encoded (f : α→β) (hf : Primrec f) :
    Primrec (fun x=>Encodable.encode (f x)) := Primrec.encode.comp hf
@[fun_prop] theorem decoded (f : α→ℕ) (hf : Primrec f) :
    Primrec (fun x=>@Encodable.decode β _ (f x)) := Primrec.decode.comp hf
@[fun_prop] theorem length (f : α→List β) (hf : Primrec f) :
    Primrec (fun x=>(f x).length) := list_length.comp hf
@[fun_prop] theorem range (f : α→ℕ) (hf : Primrec f) :
    Primrec (fun x=>List.range (f x)) := list_range.comp hf
@[fun_prop] theorem getD (f : α→List β) (g : α→ℕ) (d : β) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>(f x).getD (g x) d) := (list_getD d).comp hf hg
@[fun_prop] theorem set (f : α→List β) (g : α→ℕ) (v : α→β)
    (hf : Primrec f) (hg : Primrec g) (hv : Primrec v) :
    Primrec (fun x=>(f x).set (g x) (v x)) := list_set.comp hf (pair hg hv)
@[fun_prop] theorem append (f g : α→List β) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>f x++g x) := list_append.comp hf hg
@[fun_prop] theorem cons (f : α→β) (g : α→List β) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>f x::g x) := list_cons.comp hf hg
@[fun_prop] theorem map (f : α→List β) (g : α→β→γ) (hf : Primrec f)
    (hg : Primrec (fun p : α×β=>g p.1 p.2)) :
    Primrec (fun x=>(f x).map (g x)) := list_map hf hg.to₂
@[fun_prop] theorem flatMap (f : α→List β) (g : α→β→List γ) (hf : Primrec f)
    (hg : Primrec (fun p : α×β=>g p.1 p.2)) :
    Primrec (fun x=>(f x).flatMap (g x)) := list_flatMap hf hg.to₂
@[fun_prop] theorem foldl (f : α→List β) (g : α→γ) (h : α→γ×β→γ)
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec (fun p : α×(γ×β)=>h p.1 p.2)) :
    Primrec (fun x=>(f x).foldl (fun v b=>h x (v,b)) (g x)) := list_foldl hf hg hh.to₂
@[fun_prop] theorem bool_and (f g : α→Bool) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>f x && g x) := (Primrec.dom_finite (f:=fun p : Bool×Bool=>p.1&&p.2)).comp (pair hf hg)
@[fun_prop] theorem bool_or (f g : α→Bool) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>f x || g x) := (Primrec.dom_finite (f:=fun p : Bool×Bool=>p.1||p.2)).comp (pair hf hg)
@[fun_prop] theorem bool_not (f : α→Bool) (hf : Primrec f) :
    Primrec (fun x=> !(f x)) := (Primrec.dom_finite (f:=Bool.not)).comp hf
@[fun_prop] theorem bool_all (f : α→List β) (g : α→β→Bool) (hf : Primrec f)
    (hg : Primrec (fun p : α×β=>g p.1 p.2)) :
    Primrec (fun x=>(f x).all (g x)) := by
  have h := list_foldr hf (const true)
    ((bool_and _ _ (hg.comp (pair fst (fst.comp snd))) (snd.comp snd)).to₂)
  refine h.of_eq ?_
  intro x
  induction f x <;> simp [List.all_cons, *]

example : Primrec (fun p : ℕ×(ℕ×ℕ)=>p.1*p.2.1+p.2.2+1) := by fun_prop
example : Primrec (fun p : ℕ×List ℕ=>(List.range p.1).all fun i=>decide (p.2.getD i 0≤p.1)) := by fun_prop

end UniformKServer.PrimitiveRules

end



end OAI
