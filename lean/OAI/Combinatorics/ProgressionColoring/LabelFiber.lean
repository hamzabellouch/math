import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Lean.Elab.Tactic.Omega

namespace OAI

/-!
# Finite fibers of labels in an indexed word

Natural-number indices make differences and return times convenient. The
cardinality bridge identifies this fiber with the usual multiplicity counted
over `Fin k`, and separation of the fiber excludes every earlier return.
-/

universe uBeta

namespace QuantitativeVanDerWaerden

/-- Indices before `k` at which the word has label `l`. -/
noncomputable def labelFiber {β : Type uBeta} (k : ℕ) (f : ℕ → β) (l : β) : Finset ℕ := by
  classical
  exact (Finset.range k).filter (fun j => f j = l)

@[simp]
theorem mem_labelFiber {β : Type uBeta} {k j : ℕ} {f : ℕ → β} {l : β} :
    j ∈ labelFiber k f l ↔ j < k ∧ f j = l := by
  classical
  simp [labelFiber]

open scoped Classical in
/-- The natural-index fiber counts exactly the label multiplicity over `Fin k`. -/
theorem card_labelFiber {β : Type uBeta} (k : ℕ) (f : ℕ → β) (l : β) :
    (labelFiber k f l).card =
      (Finset.univ.filter (fun j : Fin k => f j.val = l)).card := by
  classical
  symm
  refine Finset.card_bij (fun (a : Fin k) _ => a.val) ?_ ?_ ?_
  · intro a ha
    exact mem_labelFiber.mpr ⟨a.isLt, (Finset.mem_filter.mp ha).2⟩
  · intro a ha b hb hab
    exact Fin.ext hab
  · intro b hb
    have h := mem_labelFiber.mp hb
    refine ⟨⟨b, h.1⟩, ?_, rfl⟩
    simpa using h.2

/-- A minimum positive gap between occurrences of a label rules out a return
at every positive time below that gap. -/
theorem no_earlier_label_return {β : Type uBeta} {k j h : ℕ} {f : ℕ → β} {l : β}
    (hj : j ∈ labelFiber k f l) (hjh : j + h < k)
    (hmin : ∀ a ∈ labelFiber k f l, ∀ b ∈ labelFiber k f l,
      a < b → h ≤ b - a) :
    ∀ t, 0 < t → t < h → f (j + t) ≠ l := by
  intro t ht hth hlabel
  have hmem : j + t ∈ labelFiber k f l :=
    mem_labelFiber.mpr ⟨by omega, hlabel⟩
  have hgap := hmin j hj (j + t) hmem (by omega)
  omega

end QuantitativeVanDerWaerden

end OAI
