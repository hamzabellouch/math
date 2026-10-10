import OAI.Computability.MatchingCount.ProjectionRoutine

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Block
variable {r : ℕ}
def dropTwo (k : Fin r) : Block r := (pop k).seq (pop k)
lemma dropTwo_runs (k : Fin r) (s : Store r) (a b : Bool) (l : List Bool)
    (hs : s k=a::b::l) :
    (dropTwo k).Runs s (Function.update s k l) 2 := by
  have h₁ := pop_runs k s
  have h₂ := pop_runs k (Function.update s k (s k).tail)
  have h := seq_runs _ _ h₁ h₂
  simpa [dropTwo,hs,Function.update_idem] using h

def emit (k : Fin r) : List Bool → Block r
  | [] => skip
  | b::l => (emit k l).seq (push k b)
lemma emit_runs (k : Fin r) (x : List Bool) (s : Store r) :
    (emit k x).Runs s (Function.update s k (x++s k)) (x.length+1) := by
  induction x with
  | nil => simpa [emit] using skip_runs s
  | cons b x ih =>
    have h := seq_runs _ _ ih (push_runs k b (Function.update s k (x++s k)))
    simpa [emit,Function.update_idem,Nat.add_assoc] using h
end Block
namespace Routine
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
  {f g : α → β}

noncomputable def constant (ea : α → List Bool) (eb : β → List Bool) (b : β) :
    Routine ea eb (fun _ => b) where
  scratch := 0
  block := (Block.clear 0).seq (Block.emit 0 (eb b))
  time := 2*X+C ((eb b).length+2)
  correct a := by
    have h := Block.seq_runs _ _ (Block.clear_runs (0:Fin 1)
      (Function.update (fun _ => []) 0 (ea a)))
      (Block.emit_runs (0:Fin 1) (eb b)
        (Function.update (Function.update (fun _ => []) 0 (ea a)) 0 []))
    refine ⟨2*(ea a).length+1+((eb b).length+1),?_,?_⟩
    · simpa only [eval_add,eval_mul,eval_ofNat,eval_X,eval_C,Function.update_self]
        using (show 2*(ea a).length+1+((eb b).length+1)≤2*(ea a).length+((eb b).length+2) by omega)
    · simpa only [Function.update_idem,Function.update_self,List.append_nil] using h

noncomputable def select (p : Routine ea eb f) (q : Routine ea eb g) :
    Routine (fun z : Bool×α => pairBits [z.1] (ea z.2)) eb
      (fun z => if z.1 then g z.2 else f z.2) where
  scratch := p.scratch+q.scratch
  block :=
    let ι : Fin (p.scratch+1) → Fin (p.scratch+q.scratch+1) :=
      fun i => ⟨i.val,by have := i.isLt; omega⟩
    let κ : Fin (q.scratch+1) → Fin (p.scratch+q.scratch+1) :=
      fun i => ⟨i.val,by have := i.isLt; omega⟩
    (Block.pop 0).seq (Block.cases 0 Block.skip
      ((Block.dropTwo 0).seq (p.block.rename ι))
      ((Block.dropTwo 0).seq (q.block.rename κ)))
  time := p.time+q.time+4
  correct z := by
    let R := p.scratch+q.scratch+1
    let ι : Fin (p.scratch+1) → Fin R := fun i => ⟨i.val,by have := i.isLt; omega⟩
    let κ : Fin (q.scratch+1) → Fin R := fun i => ⟨i.val,by have := i.isLt; omega⟩
    have hι : Function.Injective ι := fun i j h => Fin.ext (congrArg (fun k : Fin R => k.val) h)
    have hκ : Function.Injective κ := fun i j h => Fin.ext (congrArg (fun k : Fin R => k.val) h)
    let s₀ : Store R := Function.update (fun _ => []) 0 (pairBits [z.1] (ea z.2))
    let s₁ : Store R := Function.update (fun _ => []) 0 (z.1::true::ea z.2)
    let s₂ : Store R := Function.update (fun _ => []) 0 (ea z.2)
    have hp : (Block.pop 0).Runs s₀ s₁ 1 := by
      simpa [s₀,s₁,pairBits,Function.update_idem] using Block.pop_runs (0:Fin R) s₀
    have hd : (Block.dropTwo 0).Runs s₁ s₂ 2 := by
      simpa [s₁,s₂,Function.update_idem] using Block.dropTwo_runs (0:Fin R) s₁ z.1 true
        (ea z.2) (by simp [s₁])
    have hp₀ := p.run_at ι hι s₂ z.2 (by simp [s₂,ι]) (by
      intro i hi
      have hk : ι i≠0 := fun h => hi (hι h)
      simp [s₂,Function.update_of_ne hk])
    have hq₀ := q.run_at κ hκ s₂ z.2 (by simp [s₂,κ]) (by
      intro i hi
      have hk : κ i≠0 := fun h => hi (hκ h)
      simp [s₂,Function.update_of_ne hk])
    have hlen : (ea z.2).length≤(pairBits [z.1] (ea z.2)).length := by
      simp only [pairBits_length,List.length_singleton]
      omega
    have ht₁ := polynomial_eval_mono p.time hlen
    have ht₂ := polynomial_eval_mono q.time hlen
    rcases z with ⟨b,a⟩
    cases b with
    | false =>
      obtain ⟨t,ht,hr⟩ := hp₀
      have hx := Block.cases_runs_false (0:Fin R) Block.skip
        ((Block.dropTwo 0).seq (p.block.rename ι)) ((Block.dropTwo 0).seq (q.block.rename κ))
        (by simp [s₁]) (Block.seq_runs _ _ hd hr)
      refine ⟨1+(2+t+1),?_,?_⟩
      · simp only [eval_add,eval_ofNat]
        dsimp only at ht₁ ht₂ ht
        omega
      · simpa [s₂,ι,Function.update_idem] using Block.seq_runs _ _ hp hx
    | true =>
      obtain ⟨t,ht,hr⟩ := hq₀
      have hx := Block.cases_runs_true (0:Fin R) Block.skip
        ((Block.dropTwo 0).seq (p.block.rename ι)) ((Block.dropTwo 0).seq (q.block.rename κ))
        (by simp [s₁]) (Block.seq_runs _ _ hd hr)
      refine ⟨1+(2+t+1),?_,?_⟩
      · simp only [eval_add,eval_ofNat]
        dsimp only at ht₁ ht₂ ht
        omega
      · simpa [s₂,κ,Function.update_idem] using Block.seq_runs _ _ hp hx

end Routine
end BinaryMatching.StackCode
end

end OAI
