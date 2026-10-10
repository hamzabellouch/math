import OAI.Computability.PerfectCompleteness.Machines.ScalarTapeCardinality
import OAI.Computability.PerfectCompleteness.Sampling.PreliminarySampler
import OAI.Computability.PerfectCompleteness.Sampling.RationalFiniteLawLemmas

namespace OAI


namespace PerfectCompleteness.SamplerCardinality

open TreeSourceSpaces TreeCardinality ScalarTapeCardinality
open RecursiveSpaces DescendantSpaces HierarchicalArrays
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem stepTape_card {i : Fin (branch n)} (Root Selected : Type)
    (Ordinary : RecursiveSampler.OffPath i → Type)
    [Fintype Root] [Fintype Selected] [∀ j, Fintype (Ordinary j)] :
    Nat.card (WholeArraySampler.StepTape Root Selected Ordinary) =
      Nat.card Root * (Nat.card Selected * ∏ j, Nat.card (Ordinary j)) := by
  rw [Nat.card_pi]
  simp [WholeArraySampler.StepIndex, WholeArraySampler.StepFactor, Fintype.prod_sum_type]

def wholeTapeBound (rows repeats : Nat → Nat) (t : Nat) :
    {n m : Nat} → Path branch n m → Nat
  | n, _, .refl _ => arraysBound branch n t rows
  | n + 1, _, .step i p =>
      bucketBound rows repeats (.step i p) t *
        (wholeTapeBound rows repeats t p *
          arraysBound branch n t rows ^ Nat.card (RecursiveSampler.OffPath i))

theorem wholeTape_card_le (rows repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot),
      Nat.card (WholeArraySampler.Tape rows repeats p slots) ≤
        wholeTapeBound rows repeats t p := by
  induction p with
  | refl n =>
      intro slots
      exact arrays_card_le slots rows
  | @step n m i p ih =>
      intro slots
      change Nat.card (WholeArraySampler.StepTape
        (WholeArraySampler.RootTape rows repeats (.step i p) slots)
        (WholeArraySampler.Tape rows repeats p (childSlots slots i))
        (fun j : RecursiveSampler.OffPath i => Arrays (childSlots slots j.val) rows)) ≤ _
      rw [stepTape_card]
      apply Nat.mul_le_mul (bucket_card_le rows repeats (.step i p) slots)
      apply Nat.mul_le_mul (ih (childSlots slots i))
      calc
        _ ≤ ∏ _j : RecursiveSampler.OffPath i, arraysBound branch n t rows :=
          Finset.prod_le_prod (fun j _ => arrays_card_le (childSlots slots j.val) rows)
        _ = arraysBound branch n t rows ^ Nat.card (RecursiveSampler.OffPath i) := by
          simp [Nat.card_eq_fintype_card]

def treeTapeBound (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) : Nat :=
  ∑ leaf : Slots branch n, wholeTapeBound rows repeats t (GeometricPath.leafPath leaf)

theorem leafTape_card_le (rows repeats : Nat → Nat) (leaf : Slots branch n)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Nat.card (WholeArraySampler.Tape rows repeats (GeometricPath.leafPath leaf) slots) ≤
      treeTapeBound branch n t rows repeats := by
  apply (wholeTape_card_le rows repeats (GeometricPath.leafPath leaf) slots).trans
  change wholeTapeBound rows repeats t (GeometricPath.leafPath leaf) ≤
    ∑ other : Slots branch n, wholeTapeBound rows repeats t (GeometricPath.leafPath other)
  exact Finset.single_le_sum
    (fun other _ => Nat.zero_le (wholeTapeBound rows repeats t (GeometricPath.leafPath other)))
    (Finset.mem_univ leaf)

def testBound (n : Nat) (rows : Nat → Nat) : Nat :=
  ∑ level : Fin n, Nat.card (BucketSampler.Direction (rows (level.val + 1)))

theorem choice_card (rows : Nat → Nat) (leaf : Slots branch n) :
    Nat.card (PreliminarySampler.Choice rows leaf) = testBound n rows := by
  rw [Nat.card_sigma]
  simp only [GeometricPath.nodeAtLevel_height, testBound]

def occurrenceConstant (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) : Nat :=
  Fintype.card (Slots branch n) * treeTapeBound branch n t rows repeats * testBound n rows

theorem raw_card_le {v clausesCount : Nat}
    (clauses : Fin clausesCount → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) :
    Nat.card (PreliminarySampler.Raw clauses branch n t rows repeats) ≤
      occurrenceConstant branch n t rows repeats *
        clausesCount ^ (t * Fintype.card (Slots branch n)) := by
  rw [Nat.card_sigma]
  calc
    _ ≤ ∑ _b : PreliminarySampler.Base branch n t clausesCount,
        treeTapeBound branch n t rows repeats * testBound n rows := by
      apply Finset.sum_le_sum
      intro b _
      rw [Nat.card_prod, choice_card]
      exact Nat.mul_le_mul_right _ (leafTape_card_le rows repeats b.2
        (sourceSlots clauses (PreliminarySampler.endpoints b.1)))
    _ = Nat.card (PreliminarySampler.Base branch n t clausesCount) *
        (treeTapeBound branch n t rows repeats * testBound n rows) := by
      simp [Nat.card_eq_fintype_card]
    _ = occurrenceConstant branch n t rows repeats *
        clausesCount ^ (t * Fintype.card (Slots branch n)) := by
      rw [source_base_card]
      simp only [occurrenceConstant]
      ac_rfl

end
end PerfectCompleteness.SamplerCardinality


namespace PerfectCompleteness.SamplerRationality

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open RationalFiniteLaw
open scoped BigOperators Classical

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m t : Nat}

def recursiveTapeLaw (𝕜 : Type w) [Field 𝕜] [Finite 𝕜]
    (repeats : Nat → Nat) (p : Path branch n m) (A : Slots branch n → Type u)
    [∀ s, Finite (A s)] : RationalLaw (RecursiveSampler.tapeLaw 𝕜 repeats p A) := by
  rw [RecursiveSampler.tapeLaw_eq_uniform]
  exact RationalFiniteLaw.uniform (RecursiveSampler.Tape 𝕜 repeats p A)

def bucketTapeLaw (ℓ : Nat) (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) [∀ s, Finite (A s)] :
    RationalLaw (BucketSampler.recursiveTapeLaw ℓ repeats p A) :=
  RationalFiniteLaw.pi
    (fun _ : BucketSampler.Direction ℓ => RecursiveSampler.tapeLaw F2 repeats p A)
    (fun _ => recursiveTapeLaw F2 repeats p A)

def wholeArrayTapeLaw (rows repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot),
      RationalLaw (WholeArraySampler.tapeLaw rows repeats p slots) := by
  induction p with
  | refl n =>
      intro slots
      exact RationalFiniteLaw.uniform (Arrays slots rows)
  | @step n m i p ih =>
      intro slots
      letI : (k : WholeArraySampler.StepIndex i) → Fintype
          (WholeArraySampler.StepFactor
            (WholeArraySampler.RootTape rows repeats (.step i p) slots)
            (WholeArraySampler.Tape rows repeats p (childSlots slots i))
            (fun j => Arrays (childSlots slots j.val) rows) k) :=
        fun k => WholeArraySampler.stepFactorFintype _ _ _ k
      change RationalLaw (FiniteProduct.law (WholeArraySampler.componentLaw rows repeats i p slots))
      refine RationalFiniteLaw.pi (WholeArraySampler.componentLaw rows repeats i p slots) ?_
      intro k
      rcases k with u | (u | j)
      · exact bucketTapeLaw (rows (n + 1)) repeats (.step i p) (LeafDomain slots)
      · exact ih (childSlots slots i)
      · exact RationalFiniteLaw.uniform (Arrays (childSlots slots j.val) rows)


variable {v : Nat} {rows repeats : Nat → Nat}

def questionsLaw [NeZero m] :
    RationalLaw (PreliminarySampler.questionsLaw
      (branch := branch) (n := n) (t := t) (m := m)) :=
  RationalFiniteLaw.uniform (PreliminarySampler.Questions branch n t m)

def pathLaw (hbranch : ∀ k < n, 0 < branch k) :
    RationalLaw (GeometricPath.law n hbranch) := by
  letI := GeometricPath.slots_nonempty n hbranch
  exact RationalFiniteLaw.uniform (Slots branch n)

def baseLaw [NeZero m] (hbranch : ∀ k < n, 0 < branch k) :
    RationalLaw (PreliminarySampler.baseLaw (t := t) (m := m) hbranch) :=
  RationalFiniteLaw.product questionsLaw (pathLaw hbranch)

def choiceLaw (leaf : Slots branch n) (hn : 0 < n)
    (hrows : ∀ k, 0 < rows (k + 1)) :
    RationalLaw (PreliminarySampler.choiceLaw leaf hn hrows) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply RationalFiniteLaw.sigma (RationalFiniteLaw.uniform (Fin n))
  intro level
  letI : Nonempty (BucketSampler.Direction
      (rows (Nodes.height (GeometricPath.nodeAtLevel leaf level)))) :=
    PreliminarySampler.directionNonempty _ (by
      rw [GeometricPath.nodeAtLevel_height]
      exact hrows level.val)
  exact RationalFiniteLaw.uniform _

def conditionalLaw (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hn : 0 < n)
    (hrows : ∀ k, 0 < rows (k + 1)) (b : PreliminarySampler.Base branch n t m) :
    RationalLaw (PreliminarySampler.conditionalLaw clauses rows repeats hn hrows b) :=
  RationalFiniteLaw.product
    (wholeArrayTapeLaw rows repeats (GeometricPath.leafPath b.2)
      (sourceSlots clauses (PreliminarySampler.endpoints b.1)))
    (choiceLaw b.2 hn hrows)

def preliminaryLaw [NeZero m] (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) :
    RationalLaw (PreliminarySampler.law (t := t) clauses rows repeats hn hbranch hrows) :=
  RationalFiniteLaw.sigma (baseLaw hbranch)
    (conditionalLaw clauses rows repeats hn hrows)

theorem preliminary_positive [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    0 < (PreliminarySampler.law clauses rows repeats hn hbranch hrows).weight e :=
  RationalFiniteLaw.real_positive
    (preliminaryLaw clauses rows repeats hn hbranch hrows) e

theorem raw_nonempty [NeZero m] (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) :
    Nonempty (PreliminarySampler.Raw clauses branch n t rows repeats) := by
  let μ := PreliminarySampler.law (t := t) clauses rows repeats hn hbranch hrows
  by_contra h
  have hz : (∑ e, μ.weight e) = 0 :=
    Finset.sum_eq_zero (fun e _ => (h ⟨e⟩).elim)
  exact zero_ne_one (hz.symm.trans μ.normalized)

end
end PerfectCompleteness.SamplerRationality

end OAI
