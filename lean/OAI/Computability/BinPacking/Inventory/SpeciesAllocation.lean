import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Sum

namespace OAI

noncomputable section

namespace BinPackingGap.SpeciesAllocation

variable {Slot Species : Type*} [Fintype Slot] [DecidableEq Species]

def allocation (request : Slot → Species) (stock : Species → ℕ)
    (hcount : ∀ s, Fintype.card {b : Slot // request b = s} = stock s) :
    Slot ≃ (Σ s : Species, Fin (stock s)) :=
  (Equiv.sigmaFiberEquiv request).symm.trans
    (Equiv.sigmaCongrRight fun s =>
      (Fintype.equivFin {b : Slot // request b = s}).trans (finCongr (hcount s)))

@[simp] theorem allocation_species (request : Slot → Species) (stock : Species → ℕ)
    (hcount : ∀ s, Fintype.card {b : Slot // request b = s} = stock s) (b : Slot) :
    (allocation request stock hcount b).1 = request b := rfl

theorem exists_allocation (request : Slot → Species) (stock : Species → ℕ)
    (hcount : ∀ s, Fintype.card {b : Slot // request b = s} = stock s) :
    ∃ e : Slot ≃ (Σ s : Species, Fin (stock s)), ∀ b, (e b).1 = request b :=
  ⟨allocation request stock hcount, allocation_species request stock hcount⟩

end BinPackingGap.SpeciesAllocation

end

end OAI
