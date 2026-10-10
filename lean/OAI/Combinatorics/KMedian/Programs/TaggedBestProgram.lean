import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseSelect
import OAI.Combinatorics.KMedian.Geometry.GraphListOperations

namespace OAI


                                         
section
namespace MetricKMedian.SparseSelect.TaggedProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table)
abbrev Tag := Bool × (ℚ × Row)
def choose (x : Tag × Tag) : Bool := x.2.1 && (!x.1.1 || decide (x.2.2.1≤x.1.2.1))
@[fun_prop] theorem choose_poly : Poly choose := by unfold choose; fun_prop
def decoder (a : Tag) : Option Tag := if a.1 then some a else none
def folded (L : List Tag) : Tag := L.reverse.foldl (fun b a => if choose (b,a) then a else b) (false,(0,[]))
@[fun_prop] theorem folded_poly : Poly folded := by
  let dummy : Tag := (false,(0,[]))
  exact ⟨((listReverse enc dummy).fanout (constant (encodeList enc) enc dummy)).comp
    (listChoose choose_poly.program dummy)⟩
 theorem decode_step (a b : Tag) :
    decoder (if choose (b,a) then a else b)=
      (if a.1 then match decoder b with
        | none => some a
        | some c => some (if a.2.1≤c.2.1 then a else c)
       else decoder b) := by
  obtain ⟨pa,ca,a⟩ := a
  obtain ⟨pb,cb,b⟩ := b
  cases pa <;> cases pb <;> by_cases h : ca≤cb <;> simp [decoder,choose,h]
 theorem folded_best (L : List Tag) : decoder (folded L)=best Prod.fst (fun a => a.2.1) L := by
  unfold folded
  rw [← List.foldr_eq_foldl_reverse]
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.foldr_cons,decode_step,ih]
    cases ha : a.1 <;> cases hb : best Prod.fst (fun a => a.2.1) L <;> simp [best,ha,hb]

def raw (L : List Tag) : List Row := if (folded L).1 then [(folded L).2.2] else []
@[fun_prop] theorem raw_poly : Poly raw := by unfold raw; fun_prop
 theorem raw_best (L : List Tag) :
    raw L=((best Prod.fst (fun a => a.2.1) L).map (fun a => a.2.2)).toList := by
  rw [← folded_best]
  unfold raw decoder
  split <;> rfl
end TaggedProgram

variable {α β : Type}
theorem best_map (P : α → Bool) (cost : α → ℚ) (Q : β → Bool) (score : β → ℚ)
    (f : α → β) (hP : ∀ a,Q (f a)=P a) (hc : ∀ a,score (f a)=cost a) (L : List α) :
    (best P cost L).map f=best Q score (L.map f) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [best,List.map_cons,hP,← ih]
    split
    · cases hb : best P cost L with
      | none => rfl
      | some b =>
        simp only [Option.map_some,hc]
        split <;> rfl
    · rfl
end MetricKMedian.SparseSelect
end

end OAI
