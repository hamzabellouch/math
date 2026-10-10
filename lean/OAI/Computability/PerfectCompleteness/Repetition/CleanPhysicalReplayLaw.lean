import OAI.Computability.PerfectCompleteness.Repetition.CleanPhysicalReplay
import OAI.Computability.PerfectCompleteness.Sampling.FilledUniformSampler

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalReplayLaw

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {root h t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))
  (outside : Slots branch root → Fin t → MixedSupport.Slot)
  (placeholder inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)

theorem physicalTape_eq_filledSplitEquiv
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows) :
    CleanPhysicalReplay.physicalTape rows repeats p outside placeholder inside external children =
      FilledUniformSampler.filledSplitEquiv rows repeats p outside placeholder inside
        (external, children) := by
  apply congrArg (WholeCutGrouping.splitTape rows repeats p
    (CutSlotAssembly.fill p outside inside)).symm
  apply Prod.ext
  · rfl
  · funext i
    exact eq_of_heq ((CleanPhysicalReplay.fillChild_heq rows repeats p outside inside i
      (children i)).trans
        (FilledUniformSampler.childrenEquiv_heq rows repeats p outside inside children i).symm)

theorem physicalTape_law :
    ((FiniteDistribution.uniform
      (CleanPhysicalReplay.Exterior rows repeats p outside placeholder)).product
        (CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats p) inside rows)).pushforward
          (fun x => CleanPhysicalReplay.physicalTape rows repeats p outside placeholder inside x.1 x.2) =
      WholeCutSampler.tapeLaw rows repeats p (CutSlotAssembly.fill p outside inside) := by
  have hmap : (fun x : CleanPhysicalReplay.Exterior rows repeats p outside placeholder ×
      CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows =>
      CleanPhysicalReplay.physicalTape rows repeats p outside placeholder inside
      x.1 x.2) = FilledUniformSampler.filledSplitEquiv rows repeats p outside placeholder inside := by
    funext x
    exact physicalTape_eq_filledSplitEquiv rows repeats p outside placeholder inside x.1 x.2
  rw [hmap]
  exact FilledUniformSampler.filledSplitEquiv_tapeLaw rows repeats p outside placeholder inside

theorem evaluate_physicalTape_law :
    ((FiniteDistribution.uniform
      (CleanPhysicalReplay.Exterior rows repeats p outside placeholder)).product
        (CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats p) inside rows)).pushforward
          (fun x => WholeCutSampler.evaluate rows repeats p (CutSlotAssembly.fill p outside inside)
            (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder inside x.1 x.2)) =
      WholeArraySampler.law rows repeats p (CutSlotAssembly.fill p outside inside) := by
  have hmap : (fun x : CleanPhysicalReplay.Exterior rows repeats p outside placeholder ×
      CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows =>
      WholeCutSampler.evaluate rows repeats p
      (CutSlotAssembly.fill p outside inside)
      (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder inside x.1 x.2)) =
        FilledUniformSampler.evaluate rows repeats p outside placeholder inside := by
    funext x
    exact congrArg (WholeCutSampler.evaluate rows repeats p (CutSlotAssembly.fill p outside inside))
      (physicalTape_eq_filledSplitEquiv rows repeats p outside placeholder inside x.1 x.2)
  rw [hmap]
  exact FilledUniformSampler.evaluate_law rows repeats p outside placeholder inside

end
end PerfectCompleteness.CleanPhysicalReplayLaw

end

end OAI
