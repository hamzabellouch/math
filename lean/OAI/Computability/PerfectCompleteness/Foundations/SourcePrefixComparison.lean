import OAI.Computability.PerfectCompleteness.Decoding.SourceChildProjectionComparison
import OAI.Computability.PerfectCompleteness.Foundations.OriginalPrefixContinuation
import OAI.Computability.PerfectCompleteness.Sampling.CommonProductVariationLemmas

namespace OAI

section

namespace PerfectCompleteness.SourcePrefixComparison

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open SourceChildKernel
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

private theorem variation_triangle {Ω : Type*} [Fintype Ω]
    (P U Q : FiniteDistribution Ω) :
    P.totalVariation Q ≤ P.totalVariation U + U.totalVariation Q := by
  unfold FiniteDistribution.totalVariation
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => abs_sub_le (P.weight x) (U.weight x) (Q.weight x))
  rw [Finset.sum_add_distrib] at h
  linarith

private theorem sigma_product_forget {S R : Type*} {E : S → Type*}
    [Fintype S] [Fintype R] [∀ s, Fintype (E s)]
    (source : FiniteDistribution S) (exterior : (s : S) → FiniteDistribution (E s))
    (kernel : S → FiniteDistribution R) :
    (CompletionSoundness.sigmaLaw source (fun s => (exterior s).product (kernel s))).pushforward
        (fun z => (z.1, z.2.2)) = CleanConditioning.kernelJoint source kernel := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward, CompletionSoundness.sigmaLaw_probability,
    CleanConditioning.probability_kernelJoint]
  apply FiniteDistribution.expectation_congr
  intro s
  simpa only [FiniteDistribution.probability_pushforward] using
    congrArg (fun law : FiniteDistribution R => law.probability (fun r => event (s, r)))
      (FiniteDistribution.product_pushforward_snd (exterior s) (kernel s))

variable {branch : Nat → Nat} {n k t v m : Nat} {K : Type*} [Fintype K]

def hiddenError (branch : Nat → Nat) (n t calls : Nat) (rows : Nat → Nat) : ℝ :=
  Real.sqrt ((ChildBlockCardinality.bound branch n t calls rows : ℝ) ^ 2 / branch n) / 2

def error (branch : Nat → Nat) (n t calls : Nat) (rows : Nat → Nat) (β : ℝ) : ℝ :=
  SourceChildProjectionComparison.error branch n t calls rows β + hiddenError branch n t calls rows

variable (calls : Nat) (rows repeats : Nat → Nat)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

def nativeAssembledLaw (flag : Fin (branch n) → FiniteDistribution Bool)
    (sources : Sources (m := m) (t := t) designated) :
    FiniteDistribution (CutChildGrouping.Assembled (C := Fin calls)
      (parentLeftSlots clauses designated sources) rows) :=
  (FiniteProduct.law (fun i => SourceChildNativeLaw.leftLaw (C := Fin calls) (t := t)
    rows clauses designated flag i (sources i))).pushforward
      (CutChildGrouping.assemble (C := Fin calls) (parentLeftSlots clauses designated sources) rows)

def uniformLaw [NeZero m] :
    FiniteDistribution (SourcePhysicalAssemblyLaw.Observation (C := Fin calls) (t := t)
      rows clauses designated) :=
  CompletionSoundness.sigmaLaw (SourceChildQuestionLaw.sourceLaw m t designated)
    (fun sources => FiniteDistribution.uniform
      (CutChildGrouping.Assembled (C := Fin calls) (parentLeftSlots clauses designated sources) rows))

def continuedLaw [NeZero m] (ν : FiniteDistribution K) (q : K → Path branch n k)
    (hbranch : 0 < branch n) :
    FiniteDistribution (SourcePhysicalAssemblyLaw.Observation (C := Fin calls) (t := t)
      rows clauses designated) :=
  CompletionSoundness.sigmaLaw (SourceChildQuestionLaw.sourceLaw m t designated)
    (fun sources => OriginalPrefixContinuation.assembledLaw calls rows repeats
      (parentLeftSlots clauses designated sources) ν q hbranch)

theorem false_observation_law [NeZero m] :
    (SourceChildKernel.originalLaw (C := Fin calls) (t := t) rows clauses designated
        (fun _ => SourceChildNativeLaw.falseFlag)).pushforward
          (SourcePhysicalAssemblyLaw.observe rows clauses designated) =
      uniformLaw calls rows clauses designated :=
  SourcePhysicalAssemblyLaw.original_assembleLeft_false_law rows clauses designated

theorem continued_uniform_variation [NeZero m]
    (ν : FiniteDistribution K) (q : K → Path branch n k) (hbranch : 0 < branch n) :
    (continuedLaw (t := t) calls rows repeats clauses designated ν q hbranch).totalVariation
      (uniformLaw (t := t) calls rows clauses designated) ≤ hiddenError branch n t calls rows := by
  simpa only [FiniteDistribution.pushforward_id, continuedLaw, uniformLaw, hiddenError] using
    (ConditionalVariation.observed_sigma_le_const
      (SourceChildQuestionLaw.sourceLaw m t designated)
      (fun sources => OriginalPrefixContinuation.assembledLaw calls rows repeats
        (parentLeftSlots clauses designated sources) ν q hbranch)
      (fun sources => FiniteDistribution.uniform
        (CutChildGrouping.Assembled (C := Fin calls) (parentLeftSlots clauses designated sources) rows))
      (hiddenError branch n t calls rows)
      (fun sources => OriginalPrefixContinuation.assembledLaw_variation calls rows repeats
        (parentLeftSlots clauses designated sources) ν q hbranch)
      (id : SourcePhysicalAssemblyLaw.Observation (C := Fin calls) (t := t)
        rows clauses designated → _))

theorem original_variation [NeZero m] (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (ν : FiniteDistribution K) (q : K → Path branch n k) (hbranch : 0 < branch n) :
    ((SourceChildKernel.originalLaw (C := Fin calls) (t := t) rows clauses designated
      (fun _ => ProjectionPosterior.bernoulli β hβ hβ')).pushforward
        (SourcePhysicalAssemblyLaw.observe rows clauses designated)).totalVariation
      (continuedLaw calls rows repeats clauses designated ν q hbranch) ≤
        error branch n t calls rows β := by
  have hs := SourceChildProjectionComparison.original_observed_variation (C := Fin calls)
    rows clauses designated hbranch β hβ hβ'
    (id : SourcePhysicalAssemblyLaw.Observation (C := Fin calls) (t := t)
      rows clauses designated → _)
  simp only [id_eq, Fintype.card_fin] at hs
  rw [false_observation_law] at hs
  have ho := continued_uniform_variation (t := t) calls rows repeats clauses designated ν q hbranch
  rw [FiniteDistribution.totalVariation_comm] at ho
  exact (variation_triangle _ (uniformLaw calls rows clauses designated) _).trans (add_le_add hs ho)

theorem original_observed_variation [NeZero m] {Γ : Type*} [Fintype Γ]
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (ν : FiniteDistribution K) (q : K → Path branch n k) (hbranch : 0 < branch n)
    (observe : SourcePhysicalAssemblyLaw.Observation (C := Fin calls) (t := t)
      rows clauses designated → Γ) :
    ((SourceChildKernel.originalLaw (C := Fin calls) (t := t) rows clauses designated
      (fun _ => ProjectionPosterior.bernoulli β hβ hβ')).pushforward
        (fun sample => observe (SourcePhysicalAssemblyLaw.observe rows clauses designated sample))).totalVariation ((continuedLaw calls rows repeats clauses designated ν q hbranch).pushforward
        observe) ≤ error branch n t calls rows β := by
  rw [← FiniteDistribution.pushforward_comp
    (SourceChildKernel.originalLaw (C := Fin calls) (t := t) rows clauses designated
      (fun _ => ProjectionPosterior.bernoulli β hβ hβ'))
    (SourcePhysicalAssemblyLaw.observe rows clauses designated) observe]
  exact (DensityVariation.variation_pushforward_le _ _ observe).trans
    (original_variation calls rows repeats clauses designated β hβ hβ' ν q hbranch)

theorem conditional_variation (sources : Sources (m := m) (t := t) designated)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (ν : FiniteDistribution K) (q : K → Path branch n k) (hbranch : 0 < branch n) :
    (nativeAssembledLaw calls rows clauses designated
      (fun _ => ProjectionPosterior.bernoulli β hβ hβ') sources).totalVariation
        (OriginalPrefixContinuation.assembledLaw calls rows repeats
          (parentLeftSlots clauses designated sources) ν q hbranch) ≤
      error branch n t calls rows β := by
  have hs := SourceChildProjectionComparison.conditional_assembled_variation (C := Fin calls)
    rows clauses designated hbranch sources β hβ hβ'
  have ho := OriginalPrefixContinuation.assembledLaw_variation calls rows repeats
    (parentLeftSlots clauses designated sources) ν q hbranch
  rw [FiniteDistribution.totalVariation_comm] at ho
  simpa only [nativeAssembledLaw, error, hiddenError, Fintype.card_fin] using
    (variation_triangle _ (FiniteDistribution.uniform
      (CutChildGrouping.Assembled (C := Fin calls) (parentLeftSlots clauses designated sources) rows)) _).trans (add_le_add hs ho)

section Exterior

variable {E : Sources (m := m) (t := t) designated → Type*} [∀ sources, Fintype (E sources)]

abbrev ExteriorRaw :=
  Σ sources : Sources (m := m) (t := t) designated,
    E sources × SourceChildKernelJoint.RawTuple (C := Fin calls) (t := t) rows clauses designated

abbrev ExteriorObservation :=
  Σ sources : Sources (m := m) (t := t) designated,
    E sources × CutChildGrouping.Assembled (C := Fin calls)
      (parentLeftSlots clauses designated sources) rows

def originalExteriorLaw [NeZero m]
    (flag : Fin (branch n) → FiniteDistribution Bool)
    (exterior : (sources : Sources (m := m) (t := t) designated) → FiniteDistribution (E sources)) :
    FiniteDistribution (ExteriorRaw calls rows clauses designated (E := E)) :=
  CompletionSoundness.sigmaLaw (SourceChildQuestionLaw.sourceLaw m t designated)
    (fun sources => (exterior sources).product (FiniteProduct.law
      (fun i => SourceChildKernel.kernel (C := Fin calls) (t := t)
        rows clauses designated flag i (sources i))))

def observeExterior (sample : ExteriorRaw calls rows clauses designated (E := E)) :
    ExteriorObservation calls rows clauses designated (E := E) :=
  ⟨sample.1, (sample.2.1,
    SourcePhysicalAssemblyLaw.assembleLeft rows clauses designated sample.1 sample.2.2)⟩

theorem originalExteriorLaw_forget [NeZero m]
    (flag : Fin (branch n) → FiniteDistribution Bool)
    (exterior : (sources : Sources (m := m) (t := t) designated) → FiniteDistribution (E sources)) :
    (originalExteriorLaw calls rows clauses designated flag exterior).pushforward
        (fun sample => (SourceChildKernelJoint.groupEquiv rows clauses designated).symm
          (sample.1, sample.2.2)) =
      SourceChildKernel.originalLaw (C := Fin calls) (t := t) rows clauses designated flag := by
  unfold originalExteriorLaw
  rw [← FiniteDistribution.pushforward_comp
    (CompletionSoundness.sigmaLaw (SourceChildQuestionLaw.sourceLaw m t designated)
      (fun sources => (exterior sources).product (FiniteProduct.law
        (fun i => SourceChildKernel.kernel (C := Fin calls) (t := t)
          rows clauses designated flag i (sources i)))))
    (fun sample => (sample.1, sample.2.2))
    (SourceChildKernelJoint.groupEquiv rows clauses designated).symm,
    sigma_product_forget]
  have hgroup :
      (SourceChildKernel.originalLaw (C := Fin calls) (t := t)
        rows clauses designated flag).pushforward
          (SourceChildKernelJoint.groupEquiv rows clauses designated) =
      CleanConditioning.kernelJoint (SourceChildQuestionLaw.sourceLaw m t designated)
        (fun sources => FiniteProduct.law (fun i =>
          SourceChildKernel.kernel (C := Fin calls) (t := t)
            rows clauses designated flag i (sources i))) :=
    SourceChildKernelJoint.originalLaw_group (C := Fin calls) (t := t)
      rows clauses designated flag
  rw [← hgroup, FiniteDistribution.pushforward_comp]
  simp only [Equiv.symm_apply_apply]
  exact FiniteDistribution.pushforward_id _

theorem originalExteriorLaw_observe [NeZero m]
    (flag : Fin (branch n) → FiniteDistribution Bool)
    (exterior : (sources : Sources (m := m) (t := t) designated) → FiniteDistribution (E sources)) :
    (originalExteriorLaw calls rows clauses designated flag exterior).pushforward
        (observeExterior calls rows clauses designated) =
      CompletionSoundness.sigmaLaw (SourceChildQuestionLaw.sourceLaw m t designated)
        (fun sources => (exterior sources).product
          (nativeAssembledLaw calls rows clauses designated flag sources)) := by
  unfold originalExteriorLaw observeExterior
  refine (SigmaObservation.pushforward_fiber
    (S := Sources (m := m) (t := t) designated)
    (X := fun sources => E sources ×
      SourceChildKernelJoint.RawTuple (C := Fin calls) (t := t) rows clauses designated)
    (Y := fun sources => E sources × CutChildGrouping.Assembled (C := Fin calls)
      (parentLeftSlots clauses designated sources) rows)
    (SourceChildQuestionLaw.sourceLaw m t designated)
    (fun sources => (exterior sources).product (FiniteProduct.law
      (fun i => SourceChildKernel.kernel (C := Fin calls) (t := t)
        rows clauses designated flag i (sources i))))
    (fun sources sample => (sample.1,
      SourcePhysicalAssemblyLaw.assembleLeft (C := Fin calls) (t := t)
        rows clauses designated sources sample.2))).trans ?_
  apply congrArg (CompletionSoundness.sigmaLaw (SourceChildQuestionLaw.sourceLaw m t designated))
  funext sources
  have h := FiniteDistribution.product_pushforward (exterior sources)
    (FiniteProduct.law (fun i => SourceChildKernel.kernel (C := Fin calls) (t := t)
      rows clauses designated flag i (sources i))) id
    (SourcePhysicalAssemblyLaw.assembleLeft rows clauses designated sources)
  simpa only [id_eq, FiniteDistribution.pushforward_id,
    SourcePhysicalAssemblyLaw.kernels_assembleLeft, nativeAssembledLaw] using h

def continuedExteriorLaw [NeZero m]
    (exterior : (sources : Sources (m := m) (t := t) designated) → FiniteDistribution (E sources))
    (ν : FiniteDistribution K) (q : K → Path branch n k) (hbranch : 0 < branch n) :
    FiniteDistribution (ExteriorObservation calls rows clauses designated (E := E)) :=
  CompletionSoundness.sigmaLaw (SourceChildQuestionLaw.sourceLaw m t designated)
    (fun sources => (exterior sources).product
      (OriginalPrefixContinuation.assembledLaw calls rows repeats
        (parentLeftSlots clauses designated sources) ν q hbranch))

theorem exterior_observed_variation [NeZero m] {Γ : Type*} [Fintype Γ]
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (exterior : (sources : Sources (m := m) (t := t) designated) → FiniteDistribution (E sources))
    (ν : FiniteDistribution K) (q : K → Path branch n k) (hbranch : 0 < branch n)
    (observe : ExteriorObservation calls rows clauses designated (E := E) → Γ) :
    ((originalExteriorLaw calls rows clauses designated
      (fun _ => ProjectionPosterior.bernoulli β hβ hβ') exterior).pushforward
        (fun sample => observe (observeExterior calls rows clauses designated sample))).totalVariation
      ((continuedExteriorLaw calls rows repeats clauses designated exterior ν q hbranch).pushforward
        observe) ≤ error branch n t calls rows β := by
  rw [← FiniteDistribution.pushforward_comp
    (originalExteriorLaw calls rows clauses designated
      (fun _ => ProjectionPosterior.bernoulli β hβ hβ') exterior)
    (observeExterior calls rows clauses designated) observe, originalExteriorLaw_observe]
  unfold continuedExteriorLaw
  refine ConditionalVariation.observed_sigma_le_const
    (SourceChildQuestionLaw.sourceLaw m t designated) _ _ _ ?_ observe
  intro sources
  rw [CommonProductVariation.product_totalVariation]
  exact conditional_variation calls rows repeats clauses designated sources β hβ hβ' ν q hbranch

end Exterior
end
end PerfectCompleteness.SourcePrefixComparison

end

end OAI
