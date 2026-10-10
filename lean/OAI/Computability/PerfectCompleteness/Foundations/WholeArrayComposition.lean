import OAI.Computability.PerfectCompleteness.Sampling.SamplerCompositionLaws
import OAI.Computability.PerfectCompleteness.Sampling.WholeArraySampler

namespace OAI

section

namespace PerfectCompleteness.WholeArrayComposition

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArraySampler
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m k t : Nat}

def collapseRoot (rows repeats : Nat → Nat) (p : Path branch n m) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    RootTape rows repeats (p.append q) slots → RootTape rows repeats p slots :=
  fun ω direction =>
    SamplerComposition.collapseSuffix F2 repeats p q (LeafDomain slots) (ω direction)

theorem evaluate_collapseRoot (rows repeats : Nat → Nat)
    (p : Path branch n m) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ω : RootTape rows repeats (p.append q) slots) :
    BucketSampler.recursiveEvaluate (rows n) repeats p (LeafDomain slots)
        (collapseRoot rows repeats p q slots ω) =
      BucketSampler.recursiveEvaluate (rows n) repeats (p.append q) (LeafDomain slots) ω := by
  funext row
  change (∑ direction : BucketSampler.Direction (rows n), direction.val row •
    RecursiveSampler.evaluate F2 repeats p (LeafDomain slots)
      (SamplerComposition.collapseSuffix F2 repeats p q (LeafDomain slots) (ω direction))) =
    ∑ direction : BucketSampler.Direction (rows n), direction.val row •
      RecursiveSampler.evaluate F2 repeats (p.append q) (LeafDomain slots) (ω direction)
  apply Finset.sum_congr rfl
  intro direction _
  exact congrArg (fun h : H slots => direction.val row • h)
    (SamplerComposition.evaluate_collapseSuffix F2 repeats p q (LeafDomain slots) (ω direction))

def collapseSuffix (rows repeats : Nat → Nat) :
    {n m k : Nat} → (p : Path branch n m) → (q : Path branch m k) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        Tape rows repeats (p.append q) slots → Tape rows repeats p slots
  | _, _, _, .refl _, q, slots, ω => evaluate rows repeats q slots ω
  | _, _, _, .step i p, q, slots, ω => fun field =>
      match field with
      | .inl _ => collapseRoot rows repeats (.step i p) q slots (ω (.inl ()))
      | .inr (.inl _) =>
          collapseSuffix rows repeats p q (childSlots slots i) (ω (.inr (.inl ())))
      | .inr (.inr j) => ω (.inr (.inr j))

@[simp] theorem collapseSuffix_refl (rows repeats : Nat → Nat) (q : Path branch n k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats q slots) :
    collapseSuffix rows repeats (.refl n) q slots ω = evaluate rows repeats q slots ω := rfl

@[simp] theorem collapseSuffix_root (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (q : Path branch m k)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats ((Path.step i p).append q) slots) :
    collapseSuffix rows repeats (.step i p) q slots ω (.inl ()) =
      collapseRoot rows repeats (.step i p) q slots (ω (.inl ())) := rfl

@[simp] theorem collapseSuffix_selected (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (q : Path branch m k)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats ((Path.step i p).append q) slots) :
    collapseSuffix rows repeats (.step i p) q slots ω (.inr (.inl ())) =
      collapseSuffix rows repeats p q (childSlots slots i) (ω (.inr (.inl ()))) := rfl

@[simp] theorem collapseSuffix_ordinary (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (q : Path branch m k)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats ((Path.step i p).append q) slots) (j : RecursiveSampler.OffPath i) :
    collapseSuffix rows repeats (.step i p) q slots ω (.inr (.inr j)) =
      ω (.inr (.inr j)) := rfl

theorem evaluate_collapseSuffix (rows repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (q : Path branch m k) (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (ω : Tape rows repeats (p.append q) slots),
      evaluate rows repeats p slots (collapseSuffix rows repeats p q slots ω) =
        evaluate rows repeats (p.append q) slots ω := by
  induction p with
  | refl n => intro q slots ω; rfl
  | @step n m i p ih =>
      intro q slots ω
      exact congrArg₂ (assemble slots rows)
        (evaluate_collapseRoot rows repeats (.step i p) q slots (ω (.inl ())))
        (congrArg (fun selected : Arrays (childSlots slots i) rows =>
          childrenAt slots rows i selected (fun j => ω (.inr (.inr j))))
          (ih q (childSlots slots i) (ω (.inr (.inl ())))))

def collapsedRootLaw (rows repeats : Nat → Nat) (p : Path branch n m) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (RootTape rows repeats p slots) :=
  BucketSampler.tapeLaw (rows n)
    (FiniteProduct.law (SamplerComposition.factorLaw F2 repeats p q (LeafDomain slots)))

theorem collapseRoot_tapeLaw (rows repeats : Nat → Nat)
    (p : Path branch n m) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (BucketSampler.recursiveTapeLaw (rows n) repeats (p.append q) (LeafDomain slots)).pushforward
        (collapseRoot rows repeats p q slots) = collapsedRootLaw rows repeats p q slots := by
  calc
    _ = FiniteProduct.law (fun _ : BucketSampler.Direction (rows n) =>
        (RecursiveSampler.tapeLaw F2 repeats (p.append q) (LeafDomain slots)).pushforward
          (SamplerComposition.collapseSuffix F2 repeats p q (LeafDomain slots))) :=
      FiniteProduct.pushforward_map
        (fun _ : BucketSampler.Direction (rows n) =>
          RecursiveSampler.tapeLaw F2 repeats (p.append q) (LeafDomain slots))
        (fun _ => SamplerComposition.collapseSuffix F2 repeats p q (LeafDomain slots))
    _ = _ := by
      rw [SamplerComposition.collapseSuffix_tapeLaw, collapsedRootLaw, BucketSampler.tapeLaw]

def collapsedTapeLaw (rows repeats : Nat → Nat) :
    {n m k : Nat} → (p : Path branch n m) → (q : Path branch m k) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        FiniteDistribution (Tape rows repeats p slots)
  | _, _, _, .refl _, q, slots => WholeArraySampler.law rows repeats q slots
  | _, _, _, .step i p, q, slots => by
      letI : (field : StepIndex i) → Fintype
          (StepFactor (RootTape rows repeats (.step i p) slots)
            (Tape rows repeats p (childSlots slots i))
            (fun j => Arrays (childSlots slots j.val) rows) field) :=
        fun field => stepFactorFintype _ _ _ field
      exact FiniteProduct.law
        (Ω := fun field : StepIndex i =>
          StepFactor (RootTape rows repeats (.step i p) slots)
            (Tape rows repeats p (childSlots slots i))
            (fun j => Arrays (childSlots slots j.val) rows) field)
        (fun field => match field with
          | .inl _ => collapsedRootLaw rows repeats (.step i p) q slots
          | .inr (.inl _) => collapsedTapeLaw rows repeats p q (childSlots slots i)
          | .inr (.inr j) => FiniteDistribution.uniform (Arrays (childSlots slots j.val) rows))

def collapseField (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (q : Path branch m k)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    (field : StepIndex i) →
      StepFactor (RootTape rows repeats (.step i (p.append q)) slots)
        (Tape rows repeats (p.append q) (childSlots slots i))
        (fun j => Arrays (childSlots slots j.val) rows) field →
      StepFactor (RootTape rows repeats (.step i p) slots)
        (Tape rows repeats p (childSlots slots i))
        (fun j => Arrays (childSlots slots j.val) rows) field
  | .inl _ => collapseRoot rows repeats (.step i p) q slots
  | .inr (.inl _) => collapseSuffix rows repeats p q (childSlots slots i)
  | .inr (.inr _) => id

theorem collapseSuffix_step (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (q : Path branch m k)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    collapseSuffix rows repeats (.step i p) q slots =
      fun ω field => collapseField rows repeats i p q slots field (ω field) := by
  funext ω field
  rcases field with u | (u | j)
  · cases u
    rfl
  · cases u
    rfl
  · rfl

theorem collapseSuffix_tapeLaw (rows repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (q : Path branch m k) (slots : Slots branch n → Fin t → MixedSupport.Slot),
      (tapeLaw rows repeats (p.append q) slots).pushforward
          (collapseSuffix rows repeats p q slots) = collapsedTapeLaw rows repeats p q slots := by
  induction p with
  | refl n => intro q slots; rfl
  | @step n m i p ih =>
      intro q slots
      let : (field : StepIndex i) → Fintype
          (StepFactor (RootTape rows repeats (.step i (p.append q)) slots)
            (Tape rows repeats (p.append q) (childSlots slots i))
            (fun j => Arrays (childSlots slots j.val) rows) field) :=
        fun field => stepFactorFintype _ _ _ field
      let : (field : StepIndex i) → Fintype
          (StepFactor (RootTape rows repeats (.step i p) slots)
            (Tape rows repeats p (childSlots slots i))
            (fun j => Arrays (childSlots slots j.val) rows) field) :=
        fun field => stepFactorFintype _ _ _ field
      calc
        _ = FiniteProduct.law (fun field : StepIndex i =>
            (componentLaw rows repeats i (p.append q) slots field).pushforward
              (collapseField rows repeats i p q slots field)) := by
          rw [collapseSuffix_step]
          exact FiniteProduct.pushforward_map (componentLaw rows repeats i (p.append q) slots)
            (collapseField rows repeats i p q slots)
        _ = _ := by
          apply congrArg (fun laws : (field : StepIndex i) → FiniteDistribution
            (StepFactor (RootTape rows repeats (.step i p) slots)
              (Tape rows repeats p (childSlots slots i))
              (fun j => Arrays (childSlots slots j.val) rows) field) => FiniteProduct.law laws)
          funext field
          rcases field with u | (u | j)
          · cases u
            exact collapseRoot_tapeLaw rows repeats (.step i p) q slots
          · cases u
            exact ih q (childSlots slots i)
          · exact FiniteDistribution.pushforward_id _

theorem law_append (rows repeats : Nat → Nat) (p : Path branch n m) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    WholeArraySampler.law rows repeats (p.append q) slots =
      (collapsedTapeLaw rows repeats p q slots).pushforward (evaluate rows repeats p slots) := by
  calc
    _ = ((tapeLaw rows repeats (p.append q) slots).pushforward
        (collapseSuffix rows repeats p q slots)).pushforward (evaluate rows repeats p slots) := by
      rw [FiniteDistribution.pushforward_comp]
      unfold WholeArraySampler.law
      congr 1
      funext ω
      exact (evaluate_collapseSuffix rows repeats p q slots ω).symm
    _ = _ := by rw [collapseSuffix_tapeLaw]

end
end PerfectCompleteness.WholeArrayComposition

end

end OAI
