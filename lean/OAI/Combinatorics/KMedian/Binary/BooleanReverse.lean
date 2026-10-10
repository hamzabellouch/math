import Mathlib
import OAI.Combinatorics.KMedian.Binary.BooleanProducts
import OAI.Combinatorics.KMedian.Binary.BooleanListPrimitives

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace ReverseLoop
abbrev S := List Bool × List Bool
abbrev enc : S → List Bool := encodePair id id

def body (s : S) : List Bool ⊕ S :=
  if s.1.isEmpty then .inl s.2 else .inr (s.1.tail,s.1.head?.getD false::s.2)

def result (s : S) : List Bool := s.1.reverse++s.2

noncomputable def program : PolyProgram enc (encodeLoop enc id) body := by
  let first := PolyProgram.fst id id
  let last := PolyProgram.snd id id
  let hd := first.comp PolyProgram.head
  let tl := first.comp PolyProgram.tail
  let newLast := (hd.fanout last).comp PolyProgram.cons
  let recur := (tl.fanout newLast).comp (PolyProgram.injectRight enc id)
  let done := last.comp (PolyProgram.injectLeft enc id)
  exact (PolyProgram.ite (first.comp PolyProgram.isEmpty) recur done).congr _ (fun _ => rfl)

 theorem run (xs ys : List Bool) (S : ℕ) (h : 2*xs.length+1+ys.length≤S) :
    BoundedRun enc body S (xs.length+1) (xs,ys) (xs.reverse++ys) := by
  induction xs generalizing ys with
  | nil =>
      apply BoundedRun.stop
      · simpa only [enc,encodePair_length,id_eq,List.length_nil,zero_mul,zero_add] using h
      · rfl
  | cons b xs ih =>
      have hs : 2*xs.length+1+(b::ys).length≤S := by simp only [List.length_cons] at h ⊢; omega
      have hr := BoundedRun.step (ea:=enc) (f:=body)
        (a:=(b::xs,ys)) (a':=(xs,b::ys))
        (by simpa only [enc,encodePair_length,id_eq] using h) rfl (ih (b::ys) hs)
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hr

noncomputable def loop : PolyProgram enc id result :=
  program.loop result (X+1) X (fun s => by
    refine ⟨s.1.length+1,?_,?_⟩
    · simp only [eval_add,eval_X,eval_one,enc,encodePair_length,id_eq]; omega
    · simpa only [eval_X,enc,encodePair_length,id_eq,result] using run s.1 s.2 (2*s.1.length+1+s.2.length) le_rfl)

end ReverseLoop

namespace PolyProgram
noncomputable def reverse : PolyProgram id id List.reverse :=
  (((identity id).fanout (constant id id [])).comp ReverseLoop.loop).congr _
    (fun _ => List.append_nil _)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
