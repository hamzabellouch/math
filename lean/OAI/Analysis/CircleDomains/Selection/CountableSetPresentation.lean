import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Instances.Nat

namespace OAI

/-! A countable set can be indexed injectively by a closed subset of the
natural numbers, so the mark index has its usual discrete Polish structure. -/

open Set Function

noncomputable section
namespace CircleDomainRigidity

theorem countableSetPresentation {X : Type*} (D : Set X) (hD : D.Countable) :
    ∃ (I : Set ℕ) (p : I → X), IsClosed I ∧ Injective p ∧ range p = D := by
  let : Countable D := hD.to_subtype
  obtain ⟨f, hf⟩ := exists_injective_nat D
  let e : D ≃ range f := Equiv.ofInjective f hf
  let p : range f → X := fun i => (e.symm i).val
  refine ⟨range f, p, isClosed_discrete _, Subtype.val_injective.comp e.symm.injective, ?_⟩
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact (e.symm i).property
  · intro hx
    exact ⟨e ⟨x, hx⟩, by simp [p]⟩

end CircleDomainRigidity

end

end OAI
