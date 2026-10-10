import OAI.MathematicalPhysics.Heisenberg.CompletedSurface

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Onsite

theorem swap_factorization {V X : Type*} [Fintype V] (loc : V → X)
    (π : Equiv.Perm V) (hπ : ∀ v,loc (π v)=loc v) :
    ∃ L : List (V×V),(∀ e∈L,loc e.1=loc e.2) ∧
      (L.map (fun e=>Equiv.swap e.1 e.2)).prod=π := by
  classical
  generalize hn : π.support.card=n
  induction n using Nat.strong_induction_on generalizing π with
  | h n ih=>
    by_cases hp : π=1
    · subst π; exact ⟨[],by simp,by simp⟩
    obtain ⟨a,ha⟩ : ∃ a,π a≠a := by
      by_contra hf
      push Not at hf
      apply hp
      ext a
      exact hf a
    let τ:=Equiv.swap a (π a)*π
    have hτ : ∀ v,loc (τ v)=loc v := by
      intro v
      change loc (Equiv.swap a (π a) (π v))=loc v
      by_cases h1 : π v=a
      · rw [h1,Equiv.swap_apply_left]
        exact (hπ a).trans ((congrArg loc h1).symm.trans (hπ v))
      by_cases h2 : π v=π a
      · have hv : v=a:=π.injective h2
        subst v
        simp only [Equiv.swap_apply_right]
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      exact hπ v
    obtain ⟨L,hL,hprod⟩:=ih τ.support.card (by simpa [hn] using Equiv.Perm.card_support_swap_mul ha) τ hτ rfl
    refine ⟨(a,π a)::L,?_,?_⟩
    · intro e he
      rcases List.mem_cons.mp he with rfl|he
      · exact (hπ a).symm
      · exact hL e he
    · simp only [List.map_cons,List.prod_cons,hprod,τ]
      rw [←mul_assoc,Equiv.swap_mul_self,one_mul]

end Heisenberg.Onsite
end
end

end OAI
