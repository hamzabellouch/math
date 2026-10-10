import OAI.Computability.PerfectCompleteness.Construction.SourcePhysicalTaggedChildren
import OAI.Computability.PerfectCompleteness.Sampling.CutCallOriginalLaw

namespace OAI

section

namespace PerfectCompleteness.SourcePhysicalCallExtension

open scoped Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces SourceChildKernel

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

abbrev Tagged (sources : Sources (m := m) (t := t) designated) :=
  Σ flags : Fin (branch n) → Bool,
    CutChildGrouping.Raw (C := C)
      (SourcePhysicalTaggedChildren.slots clauses designated sources flags) rows

def forget (sources : Sources (m := m) (t := t) designated)
    (x : Tagged (C := Option C) rows clauses designated sources) :
    Tagged (C := C) rows clauses designated sources :=
  ⟨x.1, CutCallExtension.original
    (SourcePhysicalTaggedChildren.slots clauses designated sources x.1) rows x.2⟩

omit [Fintype C] in
@[simp] theorem forget_flags (sources : Sources (m := m) (t := t) designated)
    (x : Tagged (C := Option C) rows clauses designated sources) :
    (forget rows clauses designated sources x).1 = x.1 := rfl

theorem forget_law (flag : Fin (branch n) → FiniteDistribution Bool)
    (sources : Sources (m := m) (t := t) designated) :
    (CompletionSoundness.sigmaLaw (FiniteProduct.law flag) (fun flags =>
      CutChildGrouping.rawLaw (C := Option C)
        (SourcePhysicalTaggedChildren.slots clauses designated sources flags) rows)).pushforward
          (forget rows clauses designated sources) =
      CompletionSoundness.sigmaLaw (FiniteProduct.law flag) (fun flags =>
        CutChildGrouping.rawLaw (C := C)
          (SourcePhysicalTaggedChildren.slots clauses designated sources flags) rows) := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward,
    CompletionSoundness.sigmaLaw_probability, CompletionSoundness.sigmaLaw_probability]
  apply FiniteDistribution.expectation_congr
  intro flags
  exact CutCallOriginalLaw.original_probability
    (SourcePhysicalTaggedChildren.slots clauses designated sources flags) rows
    (fun old => event ⟨flags, old⟩)

theorem kernels_forget (flag : Fin (branch n) → FiniteDistribution Bool)
    (sources : Sources (m := m) (t := t) designated) :
    ((FiniteProduct.law (fun i =>
      kernel (C := Option C) (t := t) rows clauses designated flag i (sources i))).pushforward
        (SourcePhysicalTaggedChildren.observe rows clauses designated sources)).pushforward
          (forget rows clauses designated sources) =
      (FiniteProduct.law (fun i =>
        kernel (C := C) (t := t) rows clauses designated flag i (sources i))).pushforward
          (SourcePhysicalTaggedChildren.observe rows clauses designated sources) := by
  rw [SourcePhysicalTaggedChildren.kernels_tagged, forget_law,
    SourcePhysicalTaggedChildren.kernels_tagged]

theorem kernels_observe_forget (flag : Fin (branch n) → FiniteDistribution Bool)
    (sources : Sources (m := m) (t := t) designated) :
    (FiniteProduct.law (fun i =>
      kernel (C := Option C) (t := t) rows clauses designated flag i (sources i))).pushforward
        (fun raw => forget rows clauses designated sources
          (SourcePhysicalTaggedChildren.observe rows clauses designated sources raw)) =
      (FiniteProduct.law (fun i =>
        kernel (C := C) (t := t) rows clauses designated flag i (sources i))).pushforward
          (SourcePhysicalTaggedChildren.observe rows clauses designated sources) := by
  rw [← FiniteDistribution.pushforward_comp]
  exact kernels_forget rows clauses designated flag sources

theorem kernels_probability (flag : Fin (branch n) → FiniteDistribution Bool)
    (sources : Sources (m := m) (t := t) designated)
    (event : Tagged (C := C) rows clauses designated sources → Bool) :
    (FiniteProduct.law (fun i =>
      kernel (C := Option C) (t := t) rows clauses designated flag i (sources i))).probability
        (fun raw => event (forget rows clauses designated sources
          (SourcePhysicalTaggedChildren.observe rows clauses designated sources raw))) =
      (FiniteProduct.law (fun i =>
        kernel (C := C) (t := t) rows clauses designated flag i (sources i))).probability
          (fun raw => event
            (SourcePhysicalTaggedChildren.observe rows clauses designated sources raw)) := by
  have h := congrArg (fun μ : FiniteDistribution
      (Tagged (C := C) rows clauses designated sources) => μ.probability event)
    (kernels_observe_forget (C := C) rows clauses designated flag sources)
  simpa only [FiniteDistribution.probability_pushforward] using h

end
end PerfectCompleteness.SourcePhysicalCallExtension

end

end OAI
