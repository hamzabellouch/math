import OAI.Computability.PerfectCompleteness.Foundations.CutSlotOutside
import OAI.Computability.PerfectCompleteness.Foundations.WholeCutExteriorTransportLemmas
import OAI.Computability.PerfectCompleteness.Foundations.WholeCutGrouping

namespace OAI

section

namespace PerfectCompleteness.FilledUniformSampler

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (m + 1) → Fin t → MixedSupport.Slot)

abbrev Exterior := WholeCutGrouping.Exterior rows repeats p
  (CutSlotAssembly.fill p outside placeholder)

theorem cutSlots_fill (inside : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside) = inside := by
  funext s
  exact CutSlotAssembly.fill_at_cut p outside inside s

def exteriorEquiv (inside : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    Exterior rows repeats p outside placeholder ≃
      WholeCutGrouping.Exterior rows repeats p (CutSlotAssembly.fill p outside inside) :=
  WholeCutExteriorTransport.equiv rows repeats p
    (CutSlotAssembly.fill p outside placeholder) (CutSlotAssembly.fill p outside inside)
    (CutSlotAssembly.fill_outside_eq p outside placeholder inside)

def childrenEquiv (inside : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows ≃
      CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
        (WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside)) rows :=
  Equiv.piCongrRight (fun i => Equiv.cast (congrArg
    (fun slots => CutChildGrouping.Child (C := WholeCutCalls.Index rows repeats p) slots rows i)
    (cutSlots_fill p outside inside).symm))

@[simp] theorem childrenEquiv_apply
    (inside : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows)
    (i : Fin (branch m)) :
    childrenEquiv rows repeats p outside inside children i =
      cast (congrArg
        (fun slots => CutChildGrouping.Child (C := WholeCutCalls.Index rows repeats p) slots rows i)
        (cutSlots_fill p outside inside).symm) (children i) := rfl

theorem childrenEquiv_heq
    (inside : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows)
    (i : Fin (branch m)) :
    HEq (childrenEquiv rows repeats p outside inside children i) (children i) :=
  cast_heq _ _

def filledSplitEquiv (inside : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    (Exterior rows repeats p outside placeholder ×
      CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows) ≃
        WholeCutSampler.Tape rows repeats p (CutSlotAssembly.fill p outside inside) :=
  (Equiv.prodCongr (exteriorEquiv rows repeats p outside placeholder inside)
    (childrenEquiv rows repeats p outside inside)).trans
      (WholeCutGrouping.splitTape rows repeats p (CutSlotAssembly.fill p outside inside)).symm

theorem filledSplitEquiv_apply
    (inside : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (external : Exterior rows repeats p outside placeholder)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows) :
    filledSplitEquiv rows repeats p outside placeholder inside (external, children) =
      (WholeCutGrouping.splitTape rows repeats p (CutSlotAssembly.fill p outside inside)).symm
        (exteriorEquiv rows repeats p outside placeholder inside external,
          childrenEquiv rows repeats p outside inside children) := rfl

theorem filledSplitEquiv_tapeLaw
    (inside : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    ((FiniteDistribution.uniform (Exterior rows repeats p outside placeholder)).product
      (CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats p) inside rows)).pushforward
        (filledSplitEquiv rows repeats p outside placeholder inside) =
      WholeCutSampler.tapeLaw rows repeats p (CutSlotAssembly.fill p outside inside) := by
  unfold CutChildGrouping.rawLaw
  rw [UniformLinearImage.law_uniform, WholeCutSampler.uniform_product,
    WholeCutSampler.tapeLaw_eq_uniform, FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change 1 / (Fintype.card (Exterior rows repeats p outside placeholder ×
      CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows) : ℝ) =
    1 / (Fintype.card
      (WholeCutSampler.Tape rows repeats p (CutSlotAssembly.fill p outside inside)) : ℝ)
  rw [Fintype.card_congr (filledSplitEquiv rows repeats p outside placeholder inside)]

def evaluate (inside : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (x : Exterior rows repeats p outside placeholder ×
      CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows) :
    Arrays (CutSlotAssembly.fill p outside inside) rows :=
  WholeCutSampler.evaluate rows repeats p (CutSlotAssembly.fill p outside inside)
    (filledSplitEquiv rows repeats p outside placeholder inside x)

theorem evaluate_law (inside : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    ((FiniteDistribution.uniform (Exterior rows repeats p outside placeholder)).product
      (CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats p) inside rows)).pushforward
        (evaluate rows repeats p outside placeholder inside) =
      WholeArraySampler.law rows repeats p (CutSlotAssembly.fill p outside inside) := by
  unfold evaluate
  rw [← FiniteDistribution.pushforward_comp
    ((FiniteDistribution.uniform (Exterior rows repeats p outside placeholder)).product
      (CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats p) inside rows))
    (filledSplitEquiv rows repeats p outside placeholder inside)
    (WholeCutSampler.evaluate rows repeats p (CutSlotAssembly.fill p outside inside)),
    filledSplitEquiv_tapeLaw]
  exact WholeCutSampler.evaluate_law rows repeats p (CutSlotAssembly.fill p outside inside)

end
end PerfectCompleteness.FilledUniformSampler

end

end OAI
