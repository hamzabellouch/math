import OAI.Computability.PerfectCompleteness.Machines.MetadataFreeTapeLemmas
import OAI.Computability.PerfectCompleteness.Sampling.SamplerCardinalityLemmas

namespace OAI

section

namespace PerfectCompleteness.MetadataFreeLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces
open MetadataFreeSampler MetadataFreeTape
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n d t v m : Nat}

theorem tape_weight_eq (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (p : Path branch n d) :
    ∀ (q : PreliminarySampler.Questions branch n t m)
      (ω : WholeArraySampler.Tape rows repeats p (sourceSlots clauses q)),
      (WholeArraySampler.tapeLaw rows repeats p (sourceSlots clauses q)).weight ω =
        (WholeArraySampler.tapeLaw rows repeats p (dummyTreeSlots (sourceSigns clauses q))).weight
          (tapeEquiv clauses rows repeats p q ω) := by
  induction p with
  | refl n =>
      intro q ω
      rfl
  | @step n d i p ih =>
      intro q ω
      change (∏ k : WholeArraySampler.StepIndex i,
        (WholeArraySampler.componentLaw rows repeats i p (sourceSlots clauses q) k).weight (ω k)) =
        ∏ k : WholeArraySampler.StepIndex i,
          (WholeArraySampler.componentLaw rows repeats i p
            (dummyTreeSlots (sourceSigns clauses q)) k).weight
              (tapeEquiv clauses rows repeats (.step i p) q ω k)
      apply Finset.prod_congr rfl
      intro k _
      rcases k with u | (u | j)
      · rfl
      · cases u
        exact ih (fun leaf k => q (i, leaf) k) (ω (.inr (.inl ())))
      · rfl

theorem tapeLaw_transport (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (p : Path branch n d)
    (q : PreliminarySampler.Questions branch n t m) :
    (WholeArraySampler.tapeLaw rows repeats p (sourceSlots clauses q)).transport
        (tapeEquiv clauses rows repeats p q) =
      WholeArraySampler.tapeLaw rows repeats p (dummyTreeSlots (sourceSigns clauses q)) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro ω
  change (WholeArraySampler.tapeLaw rows repeats p (sourceSlots clauses q)).weight
      ((tapeEquiv clauses rows repeats p q).symm ω) = _
  simpa only [Equiv.apply_symm_apply] using
    tape_weight_eq clauses rows repeats p q ((tapeEquiv clauses rows repeats p q).symm ω)

abbrev SignedOutcome (signs : SignTuple branch n t) (rows repeats : Nat → Nat) :=
  Σ leaf : Slots branch n,
    WholeArraySampler.Tape rows repeats (GeometricPath.leafPath leaf) (dummyTreeSlots signs) ×
      PreliminarySampler.Choice rows leaf

def signedLaw (signs : SignTuple branch n t) (rows repeats : Nat → Nat)
    (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) : FiniteDistribution (SignedOutcome signs rows repeats) :=
  CompletionSoundness.sigmaLaw (GeometricPath.law n hbranch) fun leaf =>
    (WholeArraySampler.tapeLaw rows repeats (GeometricPath.leafPath leaf) (dummyTreeSlots signs)).product
      (PreliminarySampler.choiceLaw leaf hn hrows)

def signedRationalLaw (signs : SignTuple branch n t) (rows repeats : Nat → Nat)
    (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) :
    RationalFiniteLaw.RationalLaw (signedLaw signs rows repeats hn hbranch hrows) :=
  RationalFiniteLaw.sigma (SamplerRationality.pathLaw hbranch) fun leaf =>
    RationalFiniteLaw.product
      (SamplerRationality.wholeArrayTapeLaw rows repeats (GeometricPath.leafPath leaf)
        (dummyTreeSlots signs))
      (SamplerRationality.choiceLaw leaf hn hrows)

theorem signedLaw_positive (signs : SignTuple branch n t) (rows repeats : Nat → Nat)
    (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (e : SignedOutcome signs rows repeats) :
    0 < (signedLaw signs rows repeats hn hbranch hrows).weight e :=
  RationalFiniteLaw.real_positive (signedRationalLaw signs rows repeats hn hbranch hrows) e

def encodeOutcome (clauses : Fin m → SourceClause.NormalizedClause v) (rows repeats : Nat → Nat)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    SignedOutcome (sourceSigns clauses e.1.1) rows repeats :=
  ⟨e.1.2, tapeEquiv clauses rows repeats (GeometricPath.leafPath e.1.2) e.1.1 e.2.1, e.2.2⟩

theorem raw_weight_eq [NeZero m] (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    (PreliminarySampler.law clauses rows repeats hn hbranch hrows).weight e =
      (1 / (Fintype.card (PreliminarySampler.Questions branch n t m) : ℝ)) *
        (signedLaw (sourceSigns clauses e.1.1) rows repeats hn hbranch hrows).weight
          (encodeOutcome clauses rows repeats e) := by
  change ((1 / (Fintype.card (PreliminarySampler.Questions branch n t m) : ℝ)) *
      (GeometricPath.law n hbranch).weight e.1.2) *
      ((WholeArraySampler.tapeLaw rows repeats (GeometricPath.leafPath e.1.2)
        (sourceSlots clauses e.1.1)).weight e.2.1 *
        (PreliminarySampler.choiceLaw e.1.2 hn hrows).weight e.2.2) =
    (1 / (Fintype.card (PreliminarySampler.Questions branch n t m) : ℝ)) *
      ((GeometricPath.law n hbranch).weight e.1.2 *
        ((WholeArraySampler.tapeLaw rows repeats (GeometricPath.leafPath e.1.2)
          (dummyTreeSlots (sourceSigns clauses e.1.1))).weight
            (tapeEquiv clauses rows repeats (GeometricPath.leafPath e.1.2) e.1.1 e.2.1) *
          (PreliminarySampler.choiceLaw e.1.2 hn hrows).weight e.2.2))
  rw [tape_weight_eq clauses rows repeats (GeometricPath.leafPath e.1.2) e.1.1 e.2.1]
  exact mul_assoc _ _ _

theorem raw_weight_rational [NeZero m] (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    (PreliminarySampler.law clauses rows repeats hn hbranch hrows).weight e =
      (1 / (Fintype.card (PreliminarySampler.Questions branch n t m) : ℝ)) *
        ((signedRationalLaw (sourceSigns clauses e.1.1) rows repeats hn hbranch hrows).weights
          (encodeOutcome clauses rows repeats e) : ℝ) := by
  rw [raw_weight_eq, (signedRationalLaw (sourceSigns clauses e.1.1)
    rows repeats hn hbranch hrows).cast_weight]

def rawEquiv (clauses : Fin m → SourceClause.NormalizedClause v) (rows repeats : Nat → Nat) :
    PreliminarySampler.Raw clauses branch n t rows repeats ≃
      (Σ q : PreliminarySampler.Questions branch n t m,
        SignedOutcome (sourceSigns clauses q) rows repeats) where
  toFun e := ⟨e.1.1, encodeOutcome clauses rows repeats e⟩
  invFun y := ⟨(y.1, y.2.1),
    (tapeEquiv clauses rows repeats (GeometricPath.leafPath y.2.1) y.1).symm y.2.2.1,
    y.2.2.2⟩
  left_inv := by
    rintro ⟨⟨q, leaf⟩, ω, choice⟩
    simp only [encodeOutcome]
    exact congrArg
      (fun tape : WholeArraySampler.Tape rows repeats (GeometricPath.leafPath leaf)
          (sourceSlots clauses q) =>
        (⟨(q, leaf), tape, choice⟩ : PreliminarySampler.Raw clauses branch n t rows repeats))
      ((tapeEquiv clauses rows repeats (GeometricPath.leafPath leaf) q).symm_apply_apply ω)
  right_inv := by
    rintro ⟨q, leaf, ω, choice⟩
    simp only [encodeOutcome, Equiv.apply_symm_apply]

theorem rawLaw_transport [NeZero m] (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) :
    (PreliminarySampler.law (t := t) clauses rows repeats hn hbranch hrows).transport
        (rawEquiv clauses rows repeats) =
      CompletionSoundness.sigmaLaw PreliminarySampler.questionsLaw
        (fun q => signedLaw (sourceSigns clauses q) rows repeats hn hbranch hrows) := by
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨q, leaf, ω, choice⟩
  change (PreliminarySampler.law clauses rows repeats hn hbranch hrows).weight
      ⟨(q, leaf), (tapeEquiv clauses rows repeats (GeometricPath.leafPath leaf) q).symm ω,
        choice⟩ =
    (1 / (Fintype.card (PreliminarySampler.Questions branch n t m) : ℝ)) *
      (signedLaw (sourceSigns clauses q) rows repeats hn hbranch hrows).weight ⟨leaf, ω, choice⟩
  rw [raw_weight_eq]
  simp only [encodeOutcome, Equiv.apply_symm_apply]

end
end PerfectCompleteness.MetadataFreeLaw

end

end OAI
