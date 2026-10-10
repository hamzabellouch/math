import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryLists
import OAI.Combinatorics.KMedian.Binary.BinaryRationalHeight
import OAI.Combinatorics.KMedian.Binary.BooleanLoopFrom

namespace OAI


                                        
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace Iteration
open PolyProgram
variable {α : Type}
def iterates (f : α → α) (a : α) : ℕ → List α
  | 0 => []
  | n+1 => a::iterates f (f a) n

theorem iterates_eq (f : α → α) (a : α) (n : ℕ) :
    iterates f a n=(List.range n).map (fun i => f^[i] a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
      rw [iterates,ih,List.range_succ_eq_map,List.map_cons,List.map_map]
      congr 1

abbrev State (α : Type) := ℕ × (α × List α)
def enc (ea : α → List Bool) := encodePair Nat.bits (encodePair ea (encodeList ea))
def body (f : α → α) (s : State α) : List α ⊕ State α :=
  if s.1=0 then .inl s.2.2.reverse else .inr (s.1-1,(f s.2.1,s.2.1::s.2.2))

noncomputable def program {ea : α → List Bool} {f : α → α}
    (P : PolyProgram ea ea f) (a0 : α) :
    PolyProgram (enc ea) (encodeLoop (enc ea) (encodeList ea)) (body f) := by
  let n := fst Nat.bits (encodePair ea (encodeList ea))
  let st := snd Nat.bits (encodePair ea (encodeList ea))
  let a := st.comp (fst ea (encodeList ea))
  let bs := st.comp (snd ea (encodeList ea))
  let test := n.comp natZero
  let dec := (n.fanout (constant (enc ea) Nat.bits 1)).comp natSub
  let next := dec.fanout ((a.comp P).fanout ((a.fanout bs).comp (listCons ea)))
  let go := next.comp (injectRight (enc ea) (encodeList ea))
  let stop := (bs.comp (listReverse ea a0)).comp (injectLeft (enc ea) (encodeList ea))
  exact (ite test go stop).congr _ (fun s => by simp only [Function.comp_apply,body,decide_eq_true_eq])

def bound (N A : ℕ) := 2*(N+1)+1+2*A+1+N*(2*A+1)

theorem state_size (ea : α → List Bool) (N A n : ℕ) (a : α) (bs : List α)
    (hn : n+bs.length≤N) (ha : (ea a).length≤A) (hb : ∀ b∈bs, (ea b).length≤A) :
    (enc ea (n,(a,bs))).length ≤ bound N A := by
  have hnl : n.bits.length≤N+1 := (NatBinary.length_le_height (Nat.lt_two_pow_self.le)).trans (by omega)
  have hbl := EncodedList.length_bound ea bs A hb
  have hbn : bs.length*(2*A+1) ≤ N*(2*A+1) := Nat.mul_le_mul_right _ (by omega)
  simp only [enc,encodePair_length,bound]
  omega

theorem run (ea : α → List Bool) (f : α → α) (N A n : ℕ) (a : α) (bs : List α)
    (hn : n+bs.length≤N)
    (ha : ∀ i≤n, (ea (f^[i] a)).length≤A)
    (hb : ∀ b∈bs, (ea b).length≤A) :
    BoundedRun (enc ea) (body f) (bound N A) (n+1) (n,(a,bs))
      (bs.reverse++iterates f a n) := by
  induction n generalizing a bs with
  | zero =>
      have has : (ea a).length≤A := by simpa using ha 0 (Nat.zero_le _)
      refine BoundedRun.stop (state_size ea N A 0 a bs hn has hb) ?_
      simp [body,iterates]
  | succ n ih =>
      have has : (ea a).length≤A := by simpa using ha 0 (Nat.zero_le _)
      have hs := state_size ea N A (n+1) a bs hn has hb
      have hh := ih (f a) (a::bs) (by simp only [List.length_cons]; omega)
        (fun i hi => by simpa only [Function.iterate_succ_apply] using ha (i+1) (by omega))
        (by intro b hm; rcases List.mem_cons.mp hm with rfl|hm; exact has; exact hb b hm)
      have he : (a::bs).reverse++iterates f (f a) n=bs.reverse++iterates f a (n+1) := by
        simp only [List.reverse_cons,iterates,List.append_assoc,List.singleton_append]
      rw [he] at hh
      exact BoundedRun.step hs (by simp [body]) hh
end Iteration

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
variable {f : α → α} {start : β → α} {count : β → ℕ}

noncomputable def iteratesFrom (P : PolyProgram ea ea f) (initial : PolyProgram eb ea start)
    (steps : PolyProgram eb Nat.bits count) (a0 : α) (N A : Polynomial ℕ)
    (hn : ∀ b, count b≤N.eval (eb b).length)
    (ha : ∀ b i, i≤count b → (ea (f^[i] (start b))).length≤A.eval (eb b).length) :
    PolyProgram eb (encodeList ea) (fun b => Iteration.iterates f (start b) (count b)) := by
  let init := steps.fanout (initial.fanout (constant eb (encodeList ea) []))
  exact init.loopFrom (Iteration.program P a0) _ (N+1) (2*(N+1)+1+2*A+1+N*(2*A+1)) (fun b => by
    refine ⟨count b+1,by simp only [eval_add,eval_one]; have hh := hn b; omega,?_⟩
    have hr := Iteration.run ea f (N.eval (eb b).length) (A.eval (eb b).length) (count b) (start b) []
      (by simpa using hn b) (ha b) (by simp)
    simpa only [List.reverse_nil,List.nil_append,Iteration.enc,Iteration.bound,eval_add,eval_mul,eval_ofNat,eval_one] using hr)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
