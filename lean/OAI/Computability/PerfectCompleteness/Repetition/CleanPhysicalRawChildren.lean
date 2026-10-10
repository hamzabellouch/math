import OAI.Computability.PerfectCompleteness.Decoding.LowerProjectedOriginalSuccessLemmas
import OAI.Computability.PerfectCompleteness.Repetition.CleanPhysicalReplayLaw

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalRawChildren

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder inside : Slots branch (m + 1) → Fin t → MixedSupport.Slot)

def fillChildren
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows) :
    CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside)) rows :=
  fun i => CleanPhysicalReplay.fillChild rows repeats p outside inside i (children i)

theorem fillChildren_eq_childrenEquiv :
    fillChildren rows repeats p outside inside =
      (FilledUniformSampler.childrenEquiv rows repeats p outside inside : _ → _) := by
  funext children i
  exact eq_of_heq ((CleanPhysicalReplay.fillChild_heq rows repeats p outside inside i
    (children i)).trans
      (FilledUniformSampler.childrenEquiv_heq rows repeats p outside inside children i).symm)

theorem fillChildren_law :
    (CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats p) inside rows).pushforward
        (fillChildren rows repeats p outside inside) =
      CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats p)
        (WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside)) rows := by
  rw [fillChildren_eq_childrenEquiv]
  simp only [CutChildGrouping.rawLaw, UniformLinearImage.law_uniform]
  rw [FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro children
  change 1 / (Fintype.card
      (CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows) : ℝ) =
    1 / (Fintype.card (CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside)) rows) : ℝ)
  rw [Fintype.card_congr (FilledUniformSampler.childrenEquiv rows repeats p outside inside)]

theorem expectation_physicalTape
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder)
    (statistic : WholeCutSampler.Tape rows repeats p (CutSlotAssembly.fill p outside inside) → ℝ) :
    (CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats p) inside rows).expectation
        (fun children => statistic
          (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder inside external children)) =
      (CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats p)
        (WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside)) rows).expectation
          (fun children => statistic
            ((WholeCutGrouping.splitTape rows repeats p (CutSlotAssembly.fill p outside inside)).symm
              (CleanPhysicalReplay.exteriorAt rows repeats p outside placeholder inside external,
                children))) := by
  have h := congrArg
    (fun law : FiniteDistribution (CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
        (WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside)) rows) =>
      law.expectation (fun children => statistic
        ((WholeCutGrouping.splitTape rows repeats p (CutSlotAssembly.fill p outside inside)).symm
          (CleanPhysicalReplay.exteriorAt rows repeats p outside placeholder inside external,
            children))))
    (fillChildren_law rows repeats p outside inside)
  rw [FiniteDistribution.expectation_pushforward] at h
  exact h

theorem expectation_lowerTape (upper : Nodes branch n)
    (pDown : Path branch (Nodes.height upper) (m + 1))
    (external : CleanPhysicalReplay.Exterior rows repeats
      ((Nodes.path upper).append pDown) outside placeholder)
    (statistic : WholeCutSampler.Tape rows repeats ((Nodes.path upper).append pDown)
      (CutSlotAssembly.fill ((Nodes.path upper).append pDown) outside inside) → ℝ) :
    (CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats ((Nodes.path upper).append pDown))
      inside rows).expectation (fun children => statistic
        (CleanPhysicalReplay.physicalTape rows repeats ((Nodes.path upper).append pDown)
          outside placeholder inside external children)) =
      (CutChildGrouping.rawLaw
        (C := LowerCutPair.Calls rows repeats ((Nodes.path upper).append pDown))
        (WholeCutGrouping.cutSlots ((Nodes.path upper).append pDown)
          (CutSlotAssembly.fill ((Nodes.path upper).append pDown) outside inside)) rows).expectation
        (fun children => statistic
          (LowerPhysicalFiberSuccess.tape
            (CutSlotAssembly.fill ((Nodes.path upper).append pDown) outside inside) upper pDown
            (CleanPhysicalReplay.exteriorAt rows repeats ((Nodes.path upper).append pDown)
              outside placeholder inside external) children)) :=
  expectation_physicalTape rows repeats ((Nodes.path upper).append pDown)
    outside placeholder inside external statistic

end
end PerfectCompleteness.CleanPhysicalRawChildren

end

end OAI
