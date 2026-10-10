import Mathlib
import OAI.Geometry.HyperbolicGroups.StarModel
import OAI.Geometry.HyperbolicGroups.Pinned

namespace OAI

section
section
noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction

namespace StarModel
variable {F B A : Type*}

lemma fieldwise_iff (U : Finset F) (σ : Var (B := B) U → A) :
    PinnedAssignments.Fieldwise (field U) σ ↔ InjectiveFields U σ := by
  constructor
  · intro h f j k he
    have hh := h (.inr (j,f)) (.inr (k,f)) rfl he
    exact congrArg (fun v : B × {f : F // f ∉ U} => v.1) (Sum.inr.inj hh)
  · intro h v w ht he
    cases v with
    | inl f =>
      cases w with
      | inl g => exact congrArg Sum.inl (Subtype.ext ht)
      | inr kg => exact False.elim (kg.2.property ((show f.val = kg.2.val from ht) ▸ f.property))
    | inr jf =>
      cases w with
      | inl g => exact False.elim (jf.2.property ((show g.val = jf.2.val from ht.symm) ▸ g.property))
      | inr kg =>
        obtain ⟨j,f⟩ := jf
        obtain ⟨k,g⟩ := kg
        have hfg : f = g := Subtype.ext ht
        subst g
        exact congrArg (fun j => Sum.inr (j,f)) (h f he)

end StarModel
end HyperbolicObstruction
end
end

section

end
end

end OAI
