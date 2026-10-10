import OAI.Computability.MatchingCount.PairRoutine

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Routine
variable {α β : Type} (ea : α → List Bool) (eb : β → List Bool)

noncomputable def first :
    Routine (fun z : α×β => pairBits (ea z.1) (eb z.2)) ea Prod.fst where
  scratch := 1
  block := (Block.decodeRev 0 1).seq ((Block.clear 0).seq (Block.reverseInto 1 0))
  time := 10*X+10
  correct a := by
    let s₀ : Store 2 := Function.update (fun _ => []) 0 (pairBits (ea a.1) (eb a.2))
    let s₁ := Function.update (Function.update s₀ 0 (eb a.2)) 1 (ea a.1).reverse
    let s₂ := Function.update s₁ 0 []
    have h₁ : (Block.decodeRev 0 1).Runs s₀ s₁ (5*(ea a.1).length+2) := by
      simpa [s₁,s₀] using Block.decodeRev_runs (0:Fin 2) 1 (by decide) (ea a.1) (eb a.2)
        s₀ (by simp [s₀])
    have h₂ : (Block.clear 0).Runs s₁ s₂ (2*(eb a.2).length+1) := by
      simpa [s₁] using Block.clear_runs (0:Fin 2) s₁
    have h₃ := Block.reverseInto_runs (1:Fin 2) 0 (by decide) s₂
    have he : Function.update (Function.update s₂ 1 []) 0 ((s₂ 1).reverse++s₂ 0)=
        Function.update (fun _ => []) 0 (ea a.1) := by
      funext k
      fin_cases k <;> simp [s₂,s₁,s₀]
    rw [he] at h₃
    have hl : (s₂ 1).length=(ea a.1).length := by simp [s₂,s₁]
    rw [hl] at h₃
    refine ⟨_,?_,Block.seq_runs _ _ h₁ (Block.seq_runs _ _ h₂ h₃)⟩
    simp only [eval_add,eval_mul,eval_ofNat,eval_X,pairBits_length]
    omega

noncomputable def second :
    Routine (fun z : α×β => pairBits (ea z.1) (eb z.2)) eb Prod.snd where
  scratch := 1
  block := (Block.decodeRev 0 1).seq (Block.clear 1)
  time := 10*X+10
  correct a := by
    let s₀ : Store 2 := Function.update (fun _ => []) 0 (pairBits (ea a.1) (eb a.2))
    let s₁ := Function.update (Function.update s₀ 0 (eb a.2)) 1 (ea a.1).reverse
    have h₁ : (Block.decodeRev 0 1).Runs s₀ s₁ (5*(ea a.1).length+2) := by
      simpa [s₁,s₀] using Block.decodeRev_runs (0:Fin 2) 1 (by decide) (ea a.1) (eb a.2)
        s₀ (by simp [s₀])
    have h₂ := Block.clear_runs (1:Fin 2) s₁
    have he : Function.update s₁ 1 []=Function.update (fun _ => []) 0 (eb a.2) := by
      funext k
      fin_cases k <;> simp [s₁,s₀]
    rw [he] at h₂
    have hl : (s₁ 1).length=(ea a.1).length := by simp [s₁]
    rw [hl] at h₂
    refine ⟨_,?_,Block.seq_runs _ _ h₁ h₂⟩
    simp only [eval_add,eval_mul,eval_ofNat,eval_X,pairBits_length]
    omega

end Routine
end BinaryMatching.StackCode
end

end OAI
