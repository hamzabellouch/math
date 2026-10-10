import OAI.NumberTheory.TwoPoint.Halasz.HalaszFiberEnergy

namespace OAI

/-! Reindexing finite energies by the residue-class quotient map. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_fiber_energy_image {α β γ : Type*} (F : Finset α)
    (g : α → β) (hg : Set.InjOn g F) (f : β → γ) :
    halaszFiberEnergy (F.image g) f = halaszFiberEnergy F (fun x => f (g x)) := by
  rw [halasz_fiber_energy_rows,halasz_fiber_energy_rows,sum_image hg]
  apply sum_congr rfl
  intro x _
  rw [filter_image]
  exact card_image_of_injOn (hg.mono (filter_subset _ _))

lemma halasz_fiber_energy_natCast {α : Type*} {k : ℕ} (F : Finset α)
    (f : α → Fin k → ℕ) :
    halaszFiberEnergy F (fun x j => (f x j : ℤ)) = halaszFiberEnergy F f := by
  apply halasz_fiber_energy_congr
  intro x _ y _
  constructor
  · intro h
    funext j
    exact_mod_cast congrFun h j
  · intro h
    exact congrArg (fun v j => (v j : ℤ)) h

lemma halasz_fiber_energy_transfer {α β γ : Type*} (F : Finset α)
    (g : α → β) (hg : Set.InjOn g F) (u : α → γ) (v : β → γ)
    (hv : ∀ x∈F, v (g x)=u x) :
    halaszFiberEnergy F u = halaszFiberEnergy (F.image g) v := by
  rw [halasz_fiber_energy_image F g hg v]
  apply halasz_fiber_energy_congr
  intro x hx y hy
  rw [hv x hx,hv y hy]

end TwoPointCorrelations

end OAI
