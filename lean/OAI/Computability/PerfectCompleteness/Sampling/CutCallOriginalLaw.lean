import OAI.Computability.PerfectCompleteness.Decoding.LowerCutPairLemmas

namespace OAI

section

namespace PerfectCompleteness.CutCallOriginalLaw

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

section Original

variable {branch : Nat → Nat} {n t : Nat} {C : Type*} [Fintype C]
  (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat)

def originalLinear : CutCallExtension.Extended (C := C) slots rows →ₗ[ZMod 2]
    CutChildGrouping.Raw (C := C) slots rows where
  toFun := CutCallExtension.original slots rows
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype C] in
theorem originalLinear_surjective : Function.Surjective
    (originalLinear (C := C) slots rows) := by
  intro old
  refine ⟨fun i => (fun c => match c with
    | none => 0
    | some c => (old i).1 c, (old i).2), ?_⟩
  rfl

theorem original_law :
    (CutChildGrouping.rawLaw (C := Option C) slots rows).pushforward
        (CutCallExtension.original slots rows) =
      CutChildGrouping.rawLaw (C := C) slots rows := by
  unfold CutChildGrouping.rawLaw
  rw [UniformLinearImage.law_uniform, UniformLinearImage.law_uniform]
  exact UniformLinearImage.uniform_pushforward_linearMap
    (originalLinear slots rows) (originalLinear_surjective slots rows)

theorem original_probability (event : CutChildGrouping.Raw (C := C) slots rows → Bool) :
    (CutChildGrouping.rawLaw (C := Option C) slots rows).probability
        (fun raw => event (CutCallExtension.original slots rows raw)) =
      (CutChildGrouping.rawLaw (C := C) slots rows).probability event := by
  rw [← FiniteDistribution.probability_pushforward, original_law]

end Original

section First

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (p : DescendantSpaces.Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)

theorem first_law (exterior : Exterior rows repeats p slots) :
    (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats p))
        (cutSlots p slots) rows).pushforward
        (LowerCutPair.first rows repeats p slots exterior) =
      (CutChildGrouping.rawLaw (C := LowerCutPair.Calls rows repeats p)
        (cutSlots p slots) rows).pushforward
        (LowerCutRows.reconstruct rows repeats p slots exterior) := by
  change (CutChildGrouping.rawLaw
    (C := Option (LowerCutPair.Calls rows repeats p)) (cutSlots p slots) rows).pushforward
    (fun raw => LowerCutRows.reconstruct rows repeats p slots exterior
      (CutCallExtension.original (cutSlots p slots) rows raw)) = _
  rw [← FiniteDistribution.pushforward_comp, original_law]

theorem first_probability (exterior : Exterior rows repeats p slots)
    (event : Arrays slots rows → Bool) :
    (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats p))
        (cutSlots p slots) rows).probability
        (fun raw => event (LowerCutPair.first rows repeats p slots exterior raw)) =
      (CutChildGrouping.rawLaw (C := LowerCutPair.Calls rows repeats p)
        (cutSlots p slots) rows).probability
        (fun raw => event (LowerCutRows.reconstruct rows repeats p slots exterior raw)) := by
  exact original_probability (cutSlots p slots) rows
    (fun raw => event (LowerCutRows.reconstruct rows repeats p slots exterior raw))

end First
end
end PerfectCompleteness.CutCallOriginalLaw

end

end OAI
