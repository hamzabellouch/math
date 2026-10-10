import OAI.Computability.DegreeRigidity.Syntax.SigmaParameterizedClosure

namespace OAI

namespace TuringRigidity.BoundedDefinability
open BoundedSetTheory TransitiveNameModel
open BoundedDefinability SetModelFunctions
universe u
theorem SigmaDefinable.allMem_collection {M : ZFSet.{u}} {P : (ℕ → ZFSet.{u}) → Prop}
    (C : Context M) (hRep : SigmaReplacement M) (hC : SigmaCollection M)
    (h : SigmaDefinable M P) (a : ℕ) :
    SigmaDefinable M (fun e => ∀ x ∈ e a, P (cons x e)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  refine ⟨.allMem (2*a) (p.rename bindSlots),d,hd,?_⟩
  intro e he
  rw [SigmaFormula.realize_allMem M C.transitive C.pairing C.union C.separation
    hRep C.infinity hC _ _ _ (by
      intro i; unfold mix; split <;> first | exact he _ | exact hd _),mix_even]
  apply forall_congr'; intro x
  apply forall_congr'; intro hx
  rw [SigmaFormula.realize_rename]
  change p.Realize M (cons x (mix e d) ∘ bindSlots) ↔ _
  rw [bind_mix]
  exact hp (cons x e) (by intro i; cases i; exact C.transitive _ (he a) x hx; exact he _)

end TuringRigidity.BoundedDefinability

end OAI
