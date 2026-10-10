import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryRationalHeight
import OAI.Combinatorics.KMedian.Binary.BooleanLoopFrom

namespace OAI


                                    
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace Repeat
variable {α : Type}
abbrev enc (ea : α → List Bool) := encodePair Nat.bits ea
def body (f : α → α) (s : ℕ × α) : α ⊕ (ℕ × α) :=
  if s.1=0 then .inl s.2 else .inr (s.1-1,f s.2)

noncomputable def program {ea : α → List Bool} {f : α → α}
    (P : PolyProgram ea ea f) : PolyProgram (enc ea) (encodeLoop (enc ea) ea) (body f) := by
  open PolyProgram in
  let n := fst Nat.bits ea
  let a := snd Nat.bits ea
  let dec := (n.fanout (constant (enc ea) Nat.bits 1)).comp natSub
  let go := (dec.fanout (a.comp P)).comp (injectRight (enc ea) ea)
  let stop := a.comp (injectLeft (enc ea) ea)
  exact (ite (n.comp natZero) go stop).congr _ (fun _ => by simp only [Function.comp_apply,body,decide_eq_true_eq])

theorem run (ea : α → List Bool) (f : α → α) (N A n : ℕ) (a : α)
    (hn : n≤N) (ha : ∀ i≤n, (ea (f^[i] a)).length≤A) :
    BoundedRun (enc ea) (body f) (2*(N+1)+1+A) (n+1) (n,a) (f^[n] a) := by
  induction n generalizing a with
  | zero =>
      have has : (ea a).length≤A := by simpa using ha 0 (Nat.zero_le _)
      have hsize : (enc ea (0,a)).length ≤ 2*(N+1)+1+A := by
        simp only [enc,encodePair_length,Nat.zero_bits,List.length_nil]; omega
      exact BoundedRun.stop hsize (by simp [body])
  | succ n ih =>
      have hnl : (n+1).bits.length≤N+1 := (NatBinary.length_le_height (Nat.lt_two_pow_self.le)).trans (by omega)
      have has : (ea a).length≤A := by simpa using ha 0 (Nat.zero_le _)
      have hsize : (enc ea (n+1,a)).length ≤ 2*(N+1)+1+A := by
        simp only [enc,encodePair_length]; omega
      have hh := ih (f a) (by omega) (fun i hi => by
        simpa only [Function.iterate_succ_apply] using ha (i+1) (by omega))
      simpa only [Function.iterate_succ_apply] using
        (BoundedRun.step hsize (by simp [body]) hh)
end Repeat

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
variable {f : α → α} {start : β → α} {count : β → ℕ}
noncomputable def repeatFrom (P : PolyProgram ea ea f) (initial : PolyProgram eb ea start)
    (steps : PolyProgram eb Nat.bits count) (N A : Polynomial ℕ)
    (hn : ∀ b, count b≤N.eval (eb b).length)
    (ha : ∀ b i, i≤count b → (ea (f^[i] (start b))).length≤A.eval (eb b).length) :
    PolyProgram eb ea (fun b => f^[count b] (start b)) := by
  let init := steps.fanout initial
  exact init.loopFrom (Repeat.program P) _ (N+1) (2*(N+1)+1+A) (fun b => by
    refine ⟨count b+1,by simp only [eval_add,eval_one]; have hh := hn b; omega,?_⟩
    have hr := Repeat.run ea f (N.eval (eb b).length) (A.eval (eb b).length) (count b) (start b) (hn b) (ha b)
    simpa only [Repeat.enc,eval_add,eval_mul,eval_ofNat,eval_one] using hr)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
