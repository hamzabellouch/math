import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.IndependentSetElements

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open scoped BigOperators
open Classical
noncomputable section
variable {K M V:Type*} [Field K] [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)

include hΩ in
omit [Fintype V] in
lemma independentTerm_singleton (w:V → M) (x:V) :
    independentTerm v Ω w 1 {x}=Torus.X v Ω (w x) := by
  have hi:IsIndependent Ω w {x}:=by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a; subst b
    exact hΩ _
  simp only [independentTerm,hi,Finset.card_singleton,and_self,ite_true,setMonomial,Finset.sum_singleton]

include hΩ in
lemma independentElement_one (w:V → M) :
    independentElement v Ω w 1=∑x,Torus.X v Ω (w x) := by
  symm
  unfold independentElement
  apply Finset.sum_bij_ne_zero (fun x _ _=>({x}:Finset V))
  · intros; exact Finset.mem_univ _
  · intro x _ _ y _ _ h
    exact Finset.singleton_injective h
  · intro s _ hs
    unfold independentTerm at hs
    split_ifs at hs with H
    · obtain ⟨x,rfl⟩:=Finset.card_eq_one.mp H.2
      refine ⟨x,Finset.mem_univ _,?_,rfl⟩
      intro hh
      have Hx:=congrArg (fun F:Torus v Ω=>F (w x)) hh
      simp [Torus.X,Torus.monomial] at Hx
    · exact (hs rfl).elim
  · intro x _ _
    exact (independentTerm_singleton v Ω hΩ w x).symm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
