import OAI.Computability.PerfectCompleteness.Machines.OwnInputAffineSliceLemmas
import OAI.Computability.PerfectCompleteness.Machines.WholeArrayInteriorOwnInputLaw

namespace OAI

section

namespace PerfectCompleteness.WholeArrayRawAssembly

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open WholeArrayInteriorOwnInputLaw (fullPath exposedRead exteriorLaw)

variable {branch : Nat → Nat} {N h k t : Nat}

private def mergedBuckets (rows repeats : Nat → Nat)
    (p : Path branch N h) (q : Path branch h k) (hproper : k < h)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows h) → F2))
    (ω : WholeArraySampler.Tape rows repeats (p.append q) slots) :
    BucketSampler.Tape (rows h) (WholeArrayPositiveSplit.ScalarTape repeats p q slots) :=
  let parts := WholeArrayPositiveSplit.split rows repeats p q hproper slots W ω
  (HiddenBucketBias.splitTape W _).symm (parts.1, parts.2.1)

private theorem mergedBuckets_step (rows repeats : Nat → Nat)
    (j : Fin (branch N)) (p : Path branch N h) (q : Path branch h k)
    (hproper : k < h)
    (slots : Slots branch (N + 1) → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows h) → F2))
    (ω : WholeArraySampler.Tape rows repeats ((Path.step j p).append q) slots) :
    mergedBuckets rows repeats (.step j p) q hproper slots W ω =
      mergedBuckets rows repeats p q hproper (childSlots slots j)
        W (ω (.inr (.inl ()))) := by
  cases q with
  | refl => exact False.elim ((Nat.lt_irrefl _) hproper)
  | step i q => rfl

private theorem upper_rows_split (rows repeats : Nat → Nat) :
    ∀ {N k : Nat} (upper : Nodes branch N)
      (q : Path branch (Nodes.height upper) k) (hproper : k < Nodes.height upper)
      (slots : Slots branch N → Fin t → MixedSupport.Slot)
      (W : Submodule F2 (Block rows upper))
      (ω : WholeArraySampler.Tape rows repeats ((Nodes.path upper).append q) slots),
      BucketSampler.evaluate (rows (Nodes.height upper))
          (RecursiveSampler.evaluate F2 repeats q (LeafDomain (nodeSlots slots upper)))
          (mergedBuckets rows repeats (Nodes.path upper) q hproper slots W ω) =
        WholeArraySampler.evaluate rows repeats ((Nodes.path upper).append q) slots ω upper := by
  intro N
  induction N with
  | zero => intro k upper; exact nomatch upper
  | succ N ih =>
      intro k upper q hproper slots W ω
      cases upper with
      | inl u =>
          cases u
          cases q with
          | refl => exact False.elim ((Nat.lt_irrefl _) hproper)
          | step i q =>
              change BucketSampler.evaluate (rows (N + 1))
                (RecursiveSampler.evaluate F2 repeats (.step i q) (LeafDomain slots))
                ((HiddenBucketBias.splitTape W _).symm
                  (HiddenBucketBias.splitTape W _ (ω (.inl ())))) =
                BucketSampler.evaluate (rows (N + 1))
                  (RecursiveSampler.evaluate F2 repeats (.step i q) (LeafDomain slots))
                  (ω (.inl ()))
              exact congrArg
                (BucketSampler.evaluate (rows (N + 1))
                  (RecursiveSampler.evaluate F2 repeats (.step i q) (LeafDomain slots)))
                ((HiddenBucketBias.splitTape W _).symm_apply_apply (ω (.inl ())))
      | inr pair =>
          rcases pair with ⟨j, upper⟩
          change BucketSampler.evaluate (rows (Nodes.height upper))
            (RecursiveSampler.evaluate F2 repeats q
              (LeafDomain (nodeSlots (childSlots slots j) upper)))
            (mergedBuckets rows repeats (.step j (Nodes.path upper)) q hproper slots W ω) =
            WholeArraySampler.evaluate rows repeats (.step j ((Nodes.path upper).append q))
              slots ω (.inr (j, upper))
          exact (congrArg
            (BucketSampler.evaluate (rows (Nodes.height upper))
              (RecursiveSampler.evaluate F2 repeats q
                (LeafDomain (nodeSlots (childSlots slots j) upper))))
            (mergedBuckets_step rows repeats j (Nodes.path upper) q hproper slots W ω)).trans
              ((ih upper q hproper (childSlots slots j) W (ω (.inr (.inl ())))).trans
                (WholeArraySampler.evaluate_selected rows repeats j
                  ((Nodes.path upper).append q) slots ω upper).symm)

variable (rows repeats : Nat → Nat)
  (slots : Slots branch N → Fin t → MixedSupport.Slot)
  (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower)
  (W : Submodule F2 (Block rows upper))

theorem arrays_exposedRead
    (ω : WholeArraySampler.Tape rows repeats (fullPath upper lower cut) slots) :
    OwnInputRawAssembly.arrays slots rows upper lower W repeats cut
        (exposedRead rows repeats slots upper lower cut W ω) =
      WholeArraySampler.evaluate rows repeats (fullPath upper lower cut) slots ω := by
  have hupper := upper_rows_split rows repeats upper cut.path cut.proper slots W ω
  change OwnInputCanonicalQuery.assemble slots rows upper lower
    (BucketSampler.evaluate (rows (Nodes.height upper))
      (RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper)))
      (mergedBuckets rows repeats (Nodes.path upper) cut.path cut.proper slots W ω))
    (OwnInputCanonicalQuery.exteriorOf slots rows upper lower
      (WholeArraySampler.evaluate rows repeats (fullPath upper lower cut) slots ω)) = _
  rw [hupper]
  exact OwnInputCanonicalQuery.assemble_original slots rows upper lower _

theorem arrays_law :
    (OwnInputReference.rawLaw slots rows upper lower W repeats cut
      (exteriorLaw rows repeats slots upper lower cut)).pushforward (Γ := Arrays slots rows)
        (OwnInputRawAssembly.arrays slots rows upper lower W repeats cut) =
      WholeArraySampler.law rows repeats (fullPath upper lower cut) slots := by
  have h := congrArg
    (fun μ : FiniteDistribution (OwnInputReference.RawSample slots rows upper lower W repeats cut) =>
      μ.pushforward (Γ := Arrays slots rows)
        (OwnInputRawAssembly.arrays slots rows upper lower W repeats cut))
    (WholeArrayInteriorOwnInputLaw.exposedRead_law rows repeats slots upper lower cut W)
  rw [FiniteDistribution.pushforward_comp] at h
  have hmap : (fun ω => OwnInputRawAssembly.arrays slots rows upper lower W repeats cut
      (exposedRead rows repeats slots upper lower cut W ω)) =
      WholeArraySampler.evaluate rows repeats (fullPath upper lower cut) slots :=
    funext (arrays_exposedRead rows repeats slots upper lower cut W)
  rw [hmap] at h
  exact h.symm

theorem joint_readout_law {R : Type*} [Fintype R]
    (read : OwnInputReference.RawSample slots rows upper lower W repeats cut → R) :
    (WholeArraySampler.tapeLaw rows repeats (fullPath upper lower cut) slots).pushforward
        (Γ := Arrays slots rows × R)
        (fun ω => (WholeArraySampler.evaluate rows repeats (fullPath upper lower cut) slots ω,
          read (exposedRead rows repeats slots upper lower cut W ω))) =
      (OwnInputReference.rawLaw slots rows upper lower W repeats cut
        (exteriorLaw rows repeats slots upper lower cut)).pushforward
          (Γ := Arrays slots rows × R)
          (fun sample => (OwnInputRawAssembly.arrays slots rows upper lower W repeats cut sample,
            read sample)) := by
  have h := congrArg
    (fun μ : FiniteDistribution (OwnInputReference.RawSample slots rows upper lower W repeats cut) =>
      μ.pushforward (Γ := Arrays slots rows × R)
        (fun sample => (OwnInputRawAssembly.arrays slots rows upper lower W repeats cut sample,
          read sample)))
    (WholeArrayInteriorOwnInputLaw.exposedRead_law rows repeats slots upper lower cut W)
  rw [FiniteDistribution.pushforward_comp] at h
  simpa only [arrays_exposedRead] using h

theorem raw_probability
    (event : OwnInputReference.RawSample slots rows upper lower W repeats cut → Bool) :
    (WholeArraySampler.tapeLaw rows repeats (fullPath upper lower cut) slots).probability
        (fun ω => event (exposedRead rows repeats slots upper lower cut W ω)) =
      (OwnInputReference.rawLaw slots rows upper lower W repeats cut
        (exteriorLaw rows repeats slots upper lower cut)).probability event := by
  have h := congrArg (fun μ => FiniteDistribution.probability μ event)
    (WholeArrayInteriorOwnInputLaw.exposedRead_law rows repeats slots upper lower cut W)
  exact (FiniteDistribution.probability_pushforward _ _ event).symm.trans h

theorem raw_expectation
    (statistic : OwnInputReference.RawSample slots rows upper lower W repeats cut → ℝ) :
    (WholeArraySampler.tapeLaw rows repeats (fullPath upper lower cut) slots).expectation
        (fun ω => statistic (exposedRead rows repeats slots upper lower cut W ω)) =
      (OwnInputReference.rawLaw slots rows upper lower W repeats cut
        (exteriorLaw rows repeats slots upper lower cut)).expectation statistic := by
  have h := congrArg (fun μ => FiniteDistribution.expectation μ statistic)
    (WholeArrayInteriorOwnInputLaw.exposedRead_law rows repeats slots upper lower cut W)
  exact (FiniteDistribution.expectation_pushforward _ _ statistic).symm.trans h

theorem joint_expectation
    (statistic : Arrays slots rows →
      OwnInputReference.RawSample slots rows upper lower W repeats cut → ℝ) :
    (WholeArraySampler.tapeLaw rows repeats (fullPath upper lower cut) slots).expectation
        (fun ω => statistic
          (WholeArraySampler.evaluate rows repeats (fullPath upper lower cut) slots ω)
          (exposedRead rows repeats slots upper lower cut W ω)) =
      (OwnInputReference.rawLaw slots rows upper lower W repeats cut
        (exteriorLaw rows repeats slots upper lower cut)).expectation
        (fun sample => statistic
          (OwnInputRawAssembly.arrays slots rows upper lower W repeats cut sample) sample) := by
  simpa only [arrays_exposedRead] using raw_expectation rows repeats slots upper lower cut W
    (fun sample => statistic (OwnInputRawAssembly.arrays slots rows upper lower W repeats cut sample) sample)

end
end PerfectCompleteness.WholeArrayRawAssembly

end

end OAI
