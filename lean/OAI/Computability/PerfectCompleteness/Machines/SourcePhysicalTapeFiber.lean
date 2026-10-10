import OAI.Computability.PerfectCompleteness.Repetition.CleanPhysicalReplayLaw

namespace OAI

section

namespace PerfectCompleteness.SourcePhysicalTapeFiber

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {root h t : Nat}

theorem collapse_physicalTape_law (rows repeats : Nat → Nat)
    (p : Path branch root (h + 1))
    (outside : Slots branch root → Fin t → MixedSupport.Slot)
    (placeholder inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot) :
    ((FiniteDistribution.uniform
      (CleanPhysicalReplay.Exterior rows repeats p outside placeholder)).product
        (CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats p) inside rows)).pushforward
          (fun x => WholeCutSampler.collapse rows repeats p (CutSlotAssembly.fill p outside inside)
            (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder inside x.1 x.2)) =
      WholeArraySampler.tapeLaw rows repeats p (CutSlotAssembly.fill p outside inside) := by
  rw [← FiniteDistribution.pushforward_comp
    ((FiniteDistribution.uniform
      (CleanPhysicalReplay.Exterior rows repeats p outside placeholder)).product
        (CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats p) inside rows))
    (fun x => CleanPhysicalReplay.physicalTape rows repeats p outside placeholder inside x.1 x.2)
    (WholeCutSampler.collapse rows repeats p (CutSlotAssembly.fill p outside inside)),
    CleanPhysicalReplayLaw.physicalTape_law]
  exact WholeCutSampler.collapse_tapeLaw rows repeats p (CutSlotAssembly.fill p outside inside)

end
end PerfectCompleteness.SourcePhysicalTapeFiber

end

end OAI
