import Mathlib

namespace OAI

section
namespace PartialPermutation
namespace Tableau

noncomputable section
open Finset

def StandardFilling (α : Type*) [Fintype α] [PartialOrder α] :=
  {e : α ≃ Fin (Fintype.card α) // StrictMono e}

instance (α : Type*) [Fintype α] [PartialOrder α] : Fintype (StandardFilling α) :=
  by
    classical
    unfold StandardFilling
    infer_instance

def standardCount (μ : YoungDiagram) : ℕ :=
  Fintype.card (StandardFilling μ.cells)

def maxLine (μ : YoungDiagram) : ℕ := max (μ.rowLen 0) (μ.colLen 0)
def deficit (μ : YoungDiagram) : ℕ := μ.cells.card - maxLine μ

def chosenFilling (α : Type*) [Fintype α] [PartialOrder α] : StandardFilling α := by
  letI : Fintype (LinearExtension α) := inferInstanceAs (Fintype α)
  let e : LinearExtension α ≃o Fin (Fintype.card α) :=
    (Fintype.orderIsoFinOfCardEq (LinearExtension α) (by rfl)).symm
  refine ⟨{toFun := fun a => e (toLinearExtension a)
           invFun := fun i => (e.symm i : α)
           left_inv := ?_
           right_inv := ?_}, ?_⟩
  · intro a
    exact e.symm_apply_apply a
  · intro i
    exact e.apply_symm_apply i
  · intro a b hab
    apply e.strictMono
    apply lt_of_le_of_ne (toLinearExtension.monotone hab.le)
    intro h
    exact (ne_of_lt hab) h

lemma standardCount_pos (μ : YoungDiagram) : 0 < standardCount μ := by
  let : Nonempty (StandardFilling μ.cells) := ⟨chosenFilling _⟩
  exact Fintype.card_pos

end
end Tableau
end PartialPermutation
end

end OAI
