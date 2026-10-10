import OAI.Computability.MatchingCount.RawRoutine

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Block
variable {r : ℕ}
def lengthInto (src dst : Fin r) : Block r := loop src ((pop src).seq (push dst true))
lemma lengthInto_runs (src dst : Fin r) (hne : src≠dst) (s : Store r) :
    (lengthInto src dst).Runs s
      (Function.update (Function.update s src []) dst (unary (s src).length++s dst))
      (3*(s src).length+1) := by
  generalize hl : s src=l
  induction l generalizing s with
  | nil =>
    have he : Function.update (Function.update s src []) dst (unary 0++s dst)=s := by
      simp only [unary_zero,List.nil_append]
      rw [←hl,Function.update_eq_self,Function.update_eq_self]
    change (lengthInto src dst).Runs s
      (Function.update (Function.update s src []) dst (unary 0++s dst)) 1
    rw [he]
    exact loop_runs_empty src _ s hl
  | cons b l ih =>
    let s' := Function.update (Function.update s src l) dst (true::s dst)
    have hp : (pop src).Runs s (Function.update s src l) 1 := by
      simpa [hl] using pop_runs src s
    have ht : (push dst true).Runs (Function.update s src l) s' 1 := by
      simpa [s',hne.symm] using push_runs dst true (Function.update s src l)
    have hi := ih s' (by simp [s',hne])
    have he : Function.update (Function.update s' src []) dst (unary l.length++s' dst)=
        Function.update (Function.update s src []) dst (unary (b::l).length++s dst) := by
      funext k
      by_cases hk : k=dst
      · subst k
        simp only [Function.update_self,s',List.length_cons,unary]
        simp only [List.replicate_succ',List.append_assoc,List.singleton_append]
      · by_cases hks : k=src
        · subst k; simp [s',hne]
        · simp [s',Function.update_of_ne,hk,hks]
    rw [he] at hi
    have h := loop_runs_step src ((pop src).seq (push dst true)) (by simp [hl])
      (seq_runs _ _ hp ht) hi
    have heq : 2+(3*l.length+1)+1=3*(b::l).length+1 := by simp; omega
    rw [heq] at h
    exact h
end Block
namespace Routine
variable {α : Type}
noncomputable def codeLength (ea : α → List Bool) : Routine ea unary (fun a => (ea a).length) where
  scratch := 1
  block := (Block.lengthInto 0 1).seq (Block.reverseInto 1 0)
  time := 7*X+2
  correct a := by
    let s₀ : Store 2 := Function.update (fun _ => []) 0 (ea a)
    let s₁ := Function.update (Function.update s₀ 0 []) 1 (unary (ea a).length)
    have h₁ : (Block.lengthInto 0 1).Runs s₀ s₁ (3*(ea a).length+1) := by
      simpa [s₀,s₁] using Block.lengthInto_runs (0:Fin 2) 1 (by decide) s₀
    have h₂ := Block.reverseInto_runs (1:Fin 2) 0 (by decide) s₁
    have he : Function.update (Function.update s₁ 1 []) 0 ((s₁ 1).reverse++s₁ 0)=
        Function.update (fun _ => []) 0 (unary (ea a).length) := by
      funext k
      fin_cases k <;> simp [s₁,s₀]
    rw [he] at h₂
    have hl : (s₁ 1).length=(ea a).length := by simp [s₁]
    rw [hl] at h₂
    refine ⟨_,?_,Block.seq_runs _ _ h₁ h₂⟩
    simp only [eval_add,eval_mul,eval_ofNat,eval_X]
    omega
end Routine
end BinaryMatching.StackCode
end

end OAI
