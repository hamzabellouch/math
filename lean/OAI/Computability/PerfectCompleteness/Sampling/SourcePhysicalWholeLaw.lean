import OAI.Computability.PerfectCompleteness.Repetition.CleanPhysicalReplayLaw
import OAI.Computability.PerfectCompleteness.Sampling.RationalFiniteLawLemmas
import OAI.Computability.PerfectCompleteness.Sampling.SourceChildKernelMarginalLemmas

namespace OAI

section

namespace PerfectCompleteness.SourcePhysicalWholeLaw

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {root h t v m : Nat}
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))
  (outside : Slots branch root → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

abbrev Raw := CleanPhysicalReplay.Exterior rows repeats p outside placeholder ×
  ((i : Fin (branch h)) → SourceChildKernel.Raw
    (C := WholeCutCalls.Index rows repeats p) (t := t) rows clauses designated i)

def rawLaw (flag : Fin (branch h) → FiniteDistribution Bool)
    (sources : SourceChildKernel.Sources (m := m) (t := t) designated) :
    FiniteDistribution (Raw rows repeats p outside placeholder clauses designated) :=
  (FiniteDistribution.uniform (CleanPhysicalReplay.Exterior rows repeats p outside placeholder)).product
    (FiniteProduct.law (fun i => SourceChildKernel.kernel
      (C := WholeCutCalls.Index rows repeats p) (t := t) rows clauses designated flag i (sources i)))

def nativeBlockLaw (flag : Fin (branch h) → FiniteDistribution Bool)
    (sources : SourceChildKernel.Sources (m := m) (t := t) designated) :
    FiniteDistribution (CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (SourceChildKernel.parentLeftSlots clauses designated sources) rows) :=
  FiniteProduct.law (fun i => SourceChildNativeLaw.leftLaw
    (C := WholeCutCalls.Index rows repeats p) (t := t) rows clauses designated flag i (sources i))

def observeLeft (sources : SourceChildKernel.Sources (m := m) (t := t) designated)
    (sample : Raw rows repeats p outside placeholder clauses designated) :
    Arrays (CutSlotAssembly.fill p outside (SourceChildKernel.parentLeftSlots clauses designated sources)) rows :=
  WholeCutSampler.evaluate rows repeats p
    (CutSlotAssembly.fill p outside (SourceChildKernel.parentLeftSlots clauses designated sources))
    (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder
      (SourceChildKernel.parentLeftSlots clauses designated sources) sample.1
      (SourceChildKernel.leftChildren rows clauses designated sources sample.2))

theorem observeLeft_law (flag : Fin (branch h) → FiniteDistribution Bool)
    (sources : SourceChildKernel.Sources (m := m) (t := t) designated) :
    (rawLaw rows repeats p outside placeholder clauses designated flag sources).pushforward
      (observeLeft rows repeats p outside placeholder clauses designated sources) =
    ((FiniteDistribution.uniform (CleanPhysicalReplay.Exterior rows repeats p outside placeholder)).product
      (nativeBlockLaw rows repeats p clauses designated flag sources)).pushforward
        (fun x => WholeCutSampler.evaluate rows repeats p
          (CutSlotAssembly.fill p outside (SourceChildKernel.parentLeftSlots clauses designated sources))
          (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder
            (SourceChildKernel.parentLeftSlots clauses designated sources) x.1 x.2)) := by
  let decode := fun sample : Raw rows repeats p outside placeholder clauses designated =>
    (sample.1, SourceChildKernel.leftChildren rows clauses designated sources sample.2)
  let evaluate := fun x : CleanPhysicalReplay.Exterior rows repeats p outside placeholder ×
      CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
        (SourceChildKernel.parentLeftSlots clauses designated sources) rows =>
    WholeCutSampler.evaluate rows repeats p
      (CutSlotAssembly.fill p outside (SourceChildKernel.parentLeftSlots clauses designated sources))
      (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder
        (SourceChildKernel.parentLeftSlots clauses designated sources) x.1 x.2)
  calc
    _ = ((rawLaw rows repeats p outside placeholder clauses designated flag sources).pushforward
        decode).pushforward evaluate := (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = _ := by
      have hdecode : (rawLaw rows repeats p outside placeholder clauses designated flag sources).pushforward
          decode =
          (FiniteDistribution.uniform (CleanPhysicalReplay.Exterior rows repeats p outside placeholder)).product
            (nativeBlockLaw rows repeats p clauses designated flag sources) := by
        unfold rawLaw
        change ((FiniteDistribution.uniform
          (CleanPhysicalReplay.Exterior rows repeats p outside placeholder)).product
            (FiniteProduct.law (fun i => SourceChildKernel.kernel
              (C := WholeCutCalls.Index rows repeats p) (t := t) rows clauses designated flag i (sources i)))).pushforward
            (fun sample => ((id : CleanPhysicalReplay.Exterior rows repeats p outside placeholder →
              CleanPhysicalReplay.Exterior rows repeats p outside placeholder) sample.1,
              SourceChildKernel.leftChildren rows clauses designated sources sample.2)) = _
        rw [FiniteDistribution.product_pushforward,
          UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
            (FiniteDistribution.uniform (CleanPhysicalReplay.Exterior rows repeats p outside placeholder)),
          SourceChildNativeLaw.kernels_leftChildren]
        rfl
      rw [hdecode]

theorem nativeBlockLaw_false
    (sources : SourceChildKernel.Sources (m := m) (t := t) designated) :
    nativeBlockLaw rows repeats p clauses designated (fun _ => SourceChildNativeLaw.falseFlag) sources =
      CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats p)
        (SourceChildKernel.parentLeftSlots clauses designated sources) rows := by
  unfold nativeBlockLaw CutChildGrouping.rawLaw
  apply congrArg FiniteProduct.law
  funext i
  exact SourceChildNativeLaw.leftLaw_false rows clauses designated i (sources i)

theorem observeLeft_false_law
    (sources : SourceChildKernel.Sources (m := m) (t := t) designated) :
    (rawLaw rows repeats p outside placeholder clauses designated
      (fun _ => SourceChildNativeLaw.falseFlag) sources).pushforward
        (observeLeft rows repeats p outside placeholder clauses designated sources) =
      WholeArraySampler.law rows repeats p
        (CutSlotAssembly.fill p outside (SourceChildKernel.parentLeftSlots clauses designated sources)) := by
  rw [observeLeft_law, nativeBlockLaw_false]
  exact CleanPhysicalReplayLaw.evaluate_physicalTape_law rows repeats p outside placeholder
    (SourceChildKernel.parentLeftSlots clauses designated sources)

end
end PerfectCompleteness.SourcePhysicalWholeLaw

end

end OAI
