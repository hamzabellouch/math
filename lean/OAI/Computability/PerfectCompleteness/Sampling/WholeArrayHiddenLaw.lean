import OAI.Computability.PerfectCompleteness.Construction.HiddenBucketBias
import OAI.Computability.PerfectCompleteness.Foundations.QuarterBalanceLemmas
import OAI.Computability.PerfectCompleteness.Sampling.RationalFiniteLawLemmas
import OAI.Computability.PerfectCompleteness.Sampling.WholeArraySampler

namespace OAI

section

namespace PerfectCompleteness.WholeArrayHiddenLaw

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces HierarchicalArrays DescendantSpaces WholeArraySampler

noncomputable section

theorem product_assoc_pushforward {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) (ρ : FiniteDistribution C) :
    ((μ.product ν).product ρ).pushforward (fun z => (z.1.1, (z.1.2, z.2))) =
      μ.product (ν.product ρ) := by
  change ((μ.product ν).product ρ).pushforward (Equiv.prodAssoc A B C) = _
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨a, b, c⟩
  exact mul_assoc _ _ _

theorem product_split_first {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (hidden : FiniteDistribution C) (visible : FiniteDistribution D)
    (split : A → C × D) (hsplit : μ.pushforward split = hidden.product visible) :
    (μ.product ν).pushforward (fun z => ((split z.1).1, ((split z.1).2, z.2))) =
      hidden.product (visible.product ν) := by
  calc
    _ = ((μ.product ν).pushforward (fun z => (split z.1, z.2))).pushforward
        (fun z => (z.1.1, (z.1.2, z.2))) := by
      rw [FiniteDistribution.pushforward_comp]
    _ = (((μ.pushforward split).product (ν.pushforward id))).pushforward
        (fun z => (z.1.1, (z.1.2, z.2))) := by
      have hmap : (μ.product ν).pushforward (fun z => (split z.1, z.2)) =
          (μ.pushforward split).product (ν.pushforward id) := by
        simpa only [id_eq] using
          FiniteDistribution.product_pushforward μ ν split (id : B → B)
      rw [hmap]
    _ = ((hidden.product visible).product ν).pushforward
        (fun z => (z.1.1, (z.1.2, z.2))) := by
      rw [hsplit, FiniteDistribution.pushforward_id]
    _ = _ := product_assoc_pushforward hidden visible ν

theorem product_read_second {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) (read : B → C) :
    (μ.product ν).pushforward (fun z => (z.1, read z.2)) =
      μ.product (ν.pushforward read) := by
  simpa only [id_eq, FiniteDistribution.pushforward_id] using
    FiniteDistribution.product_pushforward μ ν (id : A → A) read

variable {branch : Nat → Nat} {n m t : Nat}

abbrev RestIndex (i : Fin (branch n)) :=
  {k : StepIndex i // k ≠ Sum.inl ()}

abbrev Factor (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot) :=
  StepFactor (i := i) (RootTape rows repeats (.step i p) slots)
    (Tape rows repeats p (childSlots slots i))
    (fun j => Arrays (childSlots slots j.val) rows)

instance factorFintype (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    (k : StepIndex i) → Fintype (Factor rows repeats i p slots k) :=
  fun k => WholeArraySampler.stepFactorFintype _ _ _ k

abbrev RestTape (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot) :=
  (k : RestIndex i) → Factor rows repeats i p slots k.val

instance restFactorFintype (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    (k : RestIndex i) → Fintype (Factor rows repeats i p slots k.val) :=
  fun k => factorFintype rows repeats i p slots k.val

instance restTapeFintype (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    Fintype (RestTape rows repeats i p slots) := by
  letI : (k : RestIndex i) → Fintype (Factor rows repeats i p slots k.val) :=
    fun k => factorFintype rows repeats i p slots k.val
  change Fintype ((k : RestIndex i) → Factor rows repeats i p slots k.val)
  infer_instance

abbrev ScalarTape (repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot) :=
  RecursiveSampler.Tape F2 repeats (.step i p) (LeafDomain slots)

instance scalarTapeFintype (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    Fintype (ScalarTape repeats i p slots) := by
  letI : (j : RecursiveSampler.DrawIndex repeats (.step i p)) →
      Fintype (RecursiveSampler.DrawSpace F2 repeats (.step i p) (LeafDomain slots) j) :=
    fun j => RecursiveSampler.drawSpaceFintype F2 repeats (.step i p) (LeafDomain slots) j
  change Fintype ((j : RecursiveSampler.DrawIndex repeats (.step i p)) →
    RecursiveSampler.DrawSpace F2 repeats (.step i p) (LeafDomain slots) j)
  infer_instance

def scalarLaw (repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    FiniteDistribution (ScalarTape repeats i p slots) :=
  RecursiveSampler.tapeLaw F2 repeats (.step i p) (LeafDomain slots)

def restLaw (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    FiniteDistribution (RestTape rows repeats i p slots) := by
  letI : (k : RestIndex i) → Fintype (Factor rows repeats i p slots k.val) :=
    fun k => factorFintype rows repeats i p slots k.val
  exact FiniteProduct.law
    (Ω := fun k : RestIndex i => Factor rows repeats i p slots k.val)
    (fun k : RestIndex i => componentLaw rows repeats i p slots k.val)

def splitRoot (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats (.step i p) slots) :
    RootTape rows repeats (.step i p) slots × RestTape rows repeats i p slots :=
  (ω (.inl ()), fun k => ω k.val)

theorem splitRoot_law (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    (WholeArraySampler.tapeLaw rows repeats (.step i p) slots).pushforward
        (splitRoot rows repeats i p slots) =
      (BucketSampler.tapeLaw (rows (n + 1)) (scalarLaw repeats i p slots)).product
        (restLaw rows repeats i p slots) := by
  let : (k : StepIndex i) → Fintype (Factor rows repeats i p slots k) :=
    fun k => WholeArraySampler.stepFactorFintype _ _ _ k
  exact SourceCoordinateSplit.coordinate_split_pushforward
    (Ω := fun k : StepIndex i => Factor rows repeats i p slots k)
    (componentLaw rows repeats i p slots)
    (Sum.inl ())

def split (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows (n + 1)) → F2))
    (ω : Tape rows repeats (.step i p) slots) :
    HiddenBucketBias.HiddenTape W (ScalarTape repeats i p slots) ×
      (HiddenBucketBias.VisibleTape W (ScalarTape repeats i p slots) ×
        RestTape rows repeats i p slots) :=
  ((HiddenBucketBias.splitTape W _ (ω (.inl ()))).1,
    ((HiddenBucketBias.splitTape W _ (ω (.inl ()))).2, fun k => ω k.val))

theorem split_law (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows (n + 1)) → F2)) :
    (WholeArraySampler.tapeLaw rows repeats (.step i p) slots).pushforward
        (split rows repeats i p slots W) =
      (HiddenBucketBias.hiddenTapeLaw W (scalarLaw repeats i p slots)).product
        ((HiddenBucketBias.visibleTapeLaw W (scalarLaw repeats i p slots)).product
          (restLaw rows repeats i p slots)) := by
  let buckets := HiddenBucketBias.splitTape W (ScalarTape repeats i p slots)
  calc
    _ = ((WholeArraySampler.tapeLaw rows repeats (.step i p) slots).pushforward
        (splitRoot rows repeats i p slots)).pushforward
          (fun z => ((buckets z.1).1, ((buckets z.1).2, z.2))) := by
      rw [FiniteDistribution.pushforward_comp]
      apply congrArg (fun f : Tape rows repeats (.step i p) slots →
          HiddenBucketBias.HiddenTape W (ScalarTape repeats i p slots) ×
            (HiddenBucketBias.VisibleTape W (ScalarTape repeats i p slots) ×
              RestTape rows repeats i p slots) =>
        (WholeArraySampler.tapeLaw rows repeats (.step i p) slots).pushforward f)
      rfl
    _ = _ := by
      rw [splitRoot_law]
      exact product_split_first _ _ _ _ buckets
        (HiddenBucketBias.split_tapeLaw_pushforward W (scalarLaw repeats i p slots))

theorem split_readout_law {E : Type*} [Fintype E]
    (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows (n + 1)) → F2))
    (read : RestTape rows repeats i p slots → E) :
    (WholeArraySampler.tapeLaw rows repeats (.step i p) slots).pushforward
        (fun ω => ((split rows repeats i p slots W ω).1,
          ((split rows repeats i p slots W ω).2.1,
            read (split rows repeats i p slots W ω).2.2))) =
      HiddenBucketBias.exposedLaw W (scalarLaw repeats i p slots)
        ((restLaw rows repeats i p slots).pushforward read) := by
  rw [← FiniteDistribution.pushforward_comp
    (WholeArraySampler.tapeLaw rows repeats (.step i p) slots)
    (split rows repeats i p slots W)
    (fun z => (z.1, (z.2.1, read z.2.2))), split_law]
  let μ := HiddenBucketBias.hiddenTapeLaw W (scalarLaw repeats i p slots)
  let ν := HiddenBucketBias.visibleTapeLaw W (scalarLaw repeats i p slots)
  let ρ := restLaw rows repeats i p slots
  have inner :
      (ν.product ρ).pushforward
          (fun z : HiddenBucketBias.VisibleTape W (ScalarTape repeats i p slots) ×
            RestTape rows repeats i p slots => (z.1, read z.2)) =
        ν.product (ρ.pushforward read) :=
    product_read_second ν ρ read
  have outer :
      (μ.product (ν.product ρ)).pushforward
          (fun z : HiddenBucketBias.HiddenTape W (ScalarTape repeats i p slots) ×
            (HiddenBucketBias.VisibleTape W (ScalarTape repeats i p slots) ×
              RestTape rows repeats i p slots) => (z.1, (z.2.1, read z.2.2))) =
        μ.product ((ν.product ρ).pushforward
          (fun z : HiddenBucketBias.VisibleTape W (ScalarTape repeats i p slots) ×
            RestTape rows repeats i p slots => (z.1, read z.2))) :=
    product_read_second μ (ν.product ρ)
      (fun z : HiddenBucketBias.VisibleTape W (ScalarTape repeats i p slots) ×
        RestTape rows repeats i p slots => (z.1, read z.2))
  exact outer.trans (congrArg
    (fun θ : FiniteDistribution
      (HiddenBucketBias.VisibleTape W (ScalarTape repeats i p slots) × E) => μ.product θ)
    inner)

end
end PerfectCompleteness.WholeArrayHiddenLaw

end

end OAI
