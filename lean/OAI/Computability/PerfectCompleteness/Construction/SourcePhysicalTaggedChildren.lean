import OAI.Computability.PerfectCompleteness.Foundations.DependentPredictionDifferenceLemmas
import OAI.Computability.PerfectCompleteness.Sampling.SourceChildKernelLaw

namespace OAI

section

namespace PerfectCompleteness.SourcePhysicalTaggedChildren

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces SourceChildKernel

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

def slots (sources : Sources (m := m) (t := t) designated)
    (flags : Fin (branch n) → Bool) :
    Slots branch (n + 1) → Fin t → MixedSupport.Slot :=
  fun leaf k => mixedSlots clauses designated leaf.1 (sources leaf.1)
    (flags leaf.1) leaf.2 k

def pack (sources : Sources (m := m) (t := t) designated) :
    ((i : Fin (branch n)) →
      SourceChildKernelLaw.Physical (C := C) (t := t) rows clauses designated i (sources i)) ≃
      Σ flags : Fin (branch n) → Bool,
        CutChildGrouping.Raw (C := C) (slots clauses designated sources flags) rows where
  toFun x := ⟨fun i => (x i).1, fun i => (x i).2⟩
  invFun x i := ⟨x.1 i, x.2 i⟩
  left_inv x := by
    funext i
    exact Sigma.eta (x i)
  right_inv x := by
    cases x
    rfl

def observe (sources : Sources (m := m) (t := t) designated)
    (raw : (i : Fin (branch n)) → Raw (C := C) (t := t) rows clauses designated i) :
    Σ flags : Fin (branch n) → Bool,
      CutChildGrouping.Raw (C := C) (slots clauses designated sources flags) rows :=
  pack rows clauses designated sources
    (fun i => SourceChildKernelLaw.physical rows clauses designated i (sources i) (raw i))

@[simp] theorem observe_fst (sources : Sources (m := m) (t := t) designated)
    (raw : (i : Fin (branch n)) → Raw (C := C) (t := t) rows clauses designated i) :
    (observe rows clauses designated sources raw).1 =
      fun i => rawProjected rows clauses designated i (raw i) := rfl

theorem slots_observe (sources : Sources (m := m) (t := t) designated)
    (raw : (i : Fin (branch n)) → Raw (C := C) (t := t) rows clauses designated i) :
    slots clauses designated sources (observe rows clauses designated sources raw).1 =
      parentRightSlots rows clauses designated sources raw := rfl

@[simp] theorem observe_snd (sources : Sources (m := m) (t := t) designated)
    (raw : (i : Fin (branch n)) → Raw (C := C) (t := t) rows clauses designated i) :
    (observe rows clauses designated sources raw).2 =
      rightChildren rows clauses designated sources raw := rfl

private theorem physicalLaw_sigma (flag : Fin (branch n) → FiniteDistribution Bool)
    (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    SourceChildKernelLaw.physicalLaw (C := C) (t := t) rows clauses designated flag i s =
      CompletionSoundness.sigmaLaw (flag i) (fun b =>
        FiniteDistribution.uniform (Block C rows (mixedSlots clauses designated i s b))) := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  unfold SourceChildKernelLaw.physicalLaw
  rw [FiniteDistribution.probability_mixture, CompletionSoundness.sigmaLaw_probability]
  apply FiniteDistribution.expectation_congr
  intro b
  exact FiniteDistribution.probability_pushforward _ _ _

theorem pack_law (flag : Fin (branch n) → FiniteDistribution Bool)
    (sources : Sources (m := m) (t := t) designated) :
    (FiniteProduct.law (fun i =>
      SourceChildKernelLaw.physicalLaw (C := C) (t := t) rows clauses designated flag i
        (sources i))).pushforward (pack rows clauses designated sources) =
      CompletionSoundness.sigmaLaw (FiniteProduct.law flag) (fun flags =>
        CutChildGrouping.rawLaw (C := C) (slots clauses designated sources flags) rows) := by
  rw [FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨flags, children⟩
  change (∏ i, (SourceChildKernelLaw.physicalLaw (C := C) (t := t)
      rows clauses designated flag i (sources i)).weight ⟨flags i, children i⟩) =
    (∏ i, (flag i).weight (flags i)) *
      (∏ i, (FiniteDistribution.uniform
        (Block C rows (mixedSlots clauses designated i (sources i) (flags i)))).weight
          (children i))
  simp_rw [physicalLaw_sigma]
  exact Finset.prod_mul_distrib

theorem kernels_tagged (flag : Fin (branch n) → FiniteDistribution Bool)
    (sources : Sources (m := m) (t := t) designated) :
    (FiniteProduct.law (fun i =>
      kernel (C := C) (t := t) rows clauses designated flag i (sources i))).pushforward
        (observe rows clauses designated sources) =
      CompletionSoundness.sigmaLaw (FiniteProduct.law flag) (fun flags =>
        CutChildGrouping.rawLaw (C := C) (slots clauses designated sources flags) rows) := by
  unfold observe
  rw [← FiniteDistribution.pushforward_comp, SourceChildKernelLaw.kernels_physical]
  exact pack_law rows clauses designated flag sources

end
end PerfectCompleteness.SourcePhysicalTaggedChildren

end

end OAI
