import OAI.Computability.MatchingCount.IterateRoutine

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Routine

noncomputable def append : Routine (fun z : List Bool×List Bool => pairBits z.1 z.2) id
    (fun z => z.1++z.2) where
  scratch := 1
  block := (Block.decodeRev 0 1).seq (Block.reverseInto 1 0)
  time := 10*X+10
  correct z := by
    let s₀ : Store 2 := Function.update (fun _ => []) 0 (pairBits z.1 z.2)
    let s₁ := Function.update (Function.update s₀ 0 z.2) 1 z.1.reverse
    have h₁ : (Block.decodeRev 0 1).Runs s₀ s₁ (5*z.1.length+2) := by
      simpa [s₁,s₀] using Block.decodeRev_runs (0:Fin 2) 1 (by decide) z.1 z.2
        s₀ (by simp [s₀])
    have h₂ := Block.reverseInto_runs (1:Fin 2) 0 (by decide) s₁
    have he : Function.update (Function.update s₁ 1 []) 0 ((s₁ 1).reverse++s₁ 0)=
        Function.update (fun _ => []) 0 (z.1++z.2) := by
      funext k
      fin_cases k <;> simp [s₁,s₀]
    rw [he] at h₂
    have hl : (s₁ 1).length=z.1.length := by simp [s₁]
    rw [hl] at h₂
    refine ⟨_,?_,Block.seq_runs _ _ h₁ h₂⟩
    simp only [eval_add,eval_mul,eval_ofNat,eval_X,pairBits_length]
    omega

noncomputable def pushBit (b : Bool) : Routine (id : List Bool → List Bool) id (List.cons b) where
  scratch := 0
  block := Block.push 0 b
  time := 1
  correct x := by
    refine ⟨1,by simp,?_⟩
    simpa [Function.update_idem] using Block.push_runs (0:Fin 1) b (Function.update (fun _ => []) 0 x)

noncomputable def tail : Routine (id : List Bool → List Bool) id List.tail where
  scratch := 0
  block := Block.pop 0
  time := 1
  correct x := by
    refine ⟨1,by simp,?_⟩
    simpa [Function.update_idem] using Block.pop_runs (0:Fin 1) (Function.update (fun _ => []) 0 x)

noncomputable def isEmpty : Routine (id : List Bool → List Bool) (fun b : Bool => [b]) List.isEmpty where
  scratch := 0
  block := Block.cases 0 (Block.push 0 true)
    ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 false))
  time := 2*X+3
  correct x := by
    let s : Store 1 := Function.update (fun _ => []) 0 x
    have hfalse := Block.seq_runs _ _ (Block.clear_runs (0:Fin 1) s)
      (Block.push_runs (0:Fin 1) false (Function.update s 0 []))
    have htrue := Block.push_runs (0:Fin 1) true s
    cases x with
    | nil =>
      have hh := Block.cases_runs_empty (0:Fin 1) (Block.push 0 true)
        ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 false)) (by simp [s]) htrue
      refine ⟨2,by simp,?_⟩
      simpa [s,Function.update_idem] using hh
    | cons b l =>
      cases b with
      | false =>
        have hh := Block.cases_runs_false (0:Fin 1) (Block.push 0 true)
          ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 false))
          (by simp [s]) hfalse
        refine ⟨2*(l.length+1)+3,?_,?_⟩
        · simp
        · simpa [s,Function.update_idem,Nat.add_assoc] using hh
      | true =>
        have hh := Block.cases_runs_true (0:Fin 1) (Block.push 0 true)
          ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 false))
          (by simp [s]) hfalse
        refine ⟨2*(l.length+1)+3,?_,?_⟩
        · simp
        · simpa [s,Function.update_idem,Nat.add_assoc] using hh

end Routine
end BinaryMatching.StackCode
end

end OAI
