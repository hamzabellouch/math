import OAI.Computability.PerfectCompleteness.Construction.CutChildGrouping
import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerRefinement
import OAI.Computability.PerfectCompleteness.Sampling.RationalFiniteLawLemmas
import OAI.Computability.PerfectCompleteness.Sampling.WholeArraySampler

namespace OAI

section

namespace PerfectCompleteness.WholeCutSampler

open TreeSourceSpaces HierarchicalArrays DescendantSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

abbrev RootTape (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :=
  BucketSampler.Direction (rows n) →
    CutSamplerRefinement.Tape F2 repeats p (LeafDomain slots)

def Tape (rows repeats : Nat → Nat) :
    {n m : Nat} → Path branch n m →
      (RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) → Type
  | 0, _, .refl _, slots => Arrays slots rows
  | n + 1, _, .refl _, slots =>
      CutChildGrouping.Raw (C := Fin (rows (n + 1))) slots rows
  | _, _, .step i p, slots =>
      RootTape rows repeats (.step i p) slots ×
        (Tape rows repeats p (childSlots slots i) ×
          ((j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows))

@[instance_reducible] def tapeFintypeAux (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) →
      (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) →
        Fintype (Tape rows repeats p slots)
  | 0, _, .refl _, slots => inferInstanceAs (Fintype (Arrays slots rows))
  | n + 1, _, .refl _, slots =>
      inferInstanceAs (Fintype (CutChildGrouping.Raw (C := Fin (rows (n + 1))) slots rows))
  | _, _, .step i p, slots =>
      letI : Fintype (Tape rows repeats p (childSlots slots i)) :=
        tapeFintypeAux rows repeats p (childSlots slots i)
      inferInstanceAs (Fintype
        (RootTape rows repeats (.step i p) slots ×
          (Tape rows repeats p (childSlots slots i) ×
            ((j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows))))

instance tapeFintype (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (Tape rows repeats p slots) := tapeFintypeAux rows repeats p slots

def zeroTape (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) →
      (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) →
        Tape rows repeats p slots
  | 0, _, .refl _, _ => fun node => nomatch node
  | _ + 1, _, .refl _, _ => fun _ => (fun _ => 0, fun _ _ => 0)
  | _, _, .step i p, slots =>
      (fun _ j => CutSamplerRefinement.zeroFactor F2 repeats (.step i p) (LeafDomain slots) j,
        zeroTape rows repeats p (childSlots slots i), fun _ _ _ => 0)

instance tapeNonempty (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    Nonempty (Tape rows repeats p slots) := ⟨zeroTape rows repeats p slots⟩

def stepEquiv (i : Fin (branch n)) (Root Selected : Type)
    (Ordinary : RecursiveSampler.OffPath i → Type) :
    (Root × (Selected × ((j : RecursiveSampler.OffPath i) → Ordinary j))) ≃
      WholeArraySampler.StepTape (i := i) Root Selected Ordinary where
  toFun x k := match k with
    | .inl _ => x.1
    | .inr (.inl _) => x.2.1
    | .inr (.inr j) => x.2.2 j
  invFun x := (x (.inl ()), x (.inr (.inl ())), fun j => x (.inr (.inr j)))
  left_inv x := rfl
  right_inv x := by
    funext k
    rcases k with u | (u | j)
    · cases u
      rfl
    · cases u
      rfl
    · rfl

def assembleArrays
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat) :
    CutChildGrouping.Assembled (C := Fin (rows (n + 1))) slots rows →ₗ[F2]
      Arrays slots rows where
  toFun x := WholeArraySampler.assemble slots rows x.1 x.2
  map_add' x y := by
    funext node
    rcases node with u | ⟨i, node⟩ <;> rfl
  map_smul' c x := by
    funext node
    rcases node with u | ⟨i, node⟩ <;> rfl

theorem assembleArrays_surjective
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat) : Function.Surjective (assembleArrays slots rows) := by
  intro arrays
  refine ⟨(arrays (.inl ()), fun i node => arrays (.inr (i, node))), ?_⟩
  funext node
  rcases node with u | ⟨i, node⟩
  · cases u
    rfl
  · rfl

def collapseRoot (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    RootTape rows repeats p slots → WholeArraySampler.RootTape rows repeats p slots :=
  fun x v => CutSamplerRefinement.collapse F2 repeats p (LeafDomain slots) (x v)

def collapse (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) →
      (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) →
        Tape rows repeats p slots → WholeArraySampler.Tape rows repeats p slots
  | 0, _, .refl _, _, x => x
  | _ + 1, _, .refl _, slots, x =>
      assembleArrays slots rows (CutChildGrouping.assemble slots rows x)
  | _, _, .step i p, slots, x =>
      stepEquiv i (WholeArraySampler.RootTape rows repeats (.step i p) slots)
        (WholeArraySampler.Tape rows repeats p (childSlots slots i))
        (fun j => Arrays (childSlots slots j.val) rows)
        (collapseRoot rows repeats (.step i p) slots x.1,
          collapse rows repeats p (childSlots slots i) x.2.1, x.2.2)

def rootLaw (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (RootTape rows repeats p slots) :=
  FiniteProduct.law (fun _ : BucketSampler.Direction (rows n) =>
    CutSamplerRefinement.tapeLaw F2 repeats p (LeafDomain slots))

def tapeLaw (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) →
      (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) →
        FiniteDistribution (Tape rows repeats p slots)
  | 0, _, .refl _, slots => FiniteDistribution.uniform (Arrays slots rows)
  | n + 1, _, .refl _, slots =>
      CutChildGrouping.rawLaw (C := Fin (rows (n + 1))) slots rows
  | _, _, .step i p, slots =>
      (rootLaw rows repeats (.step i p) slots).product
        ((tapeLaw rows repeats p (childSlots slots i)).product
          (FiniteProduct.law (fun j : RecursiveSampler.OffPath i =>
            FiniteDistribution.uniform (Arrays (childSlots slots j.val) rows))))

theorem uniform_product {R S : Type*} [Fintype R] [Fintype S]
    [Nonempty R] [Nonempty S] :
    (FiniteDistribution.uniform R).product (FiniteDistribution.uniform S) =
      FiniteDistribution.uniform (R × S) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  simp only [FiniteDistribution.product, FiniteDistribution.uniform,
    Fintype.card_prod, Nat.cast_mul, one_div_mul_one_div]

theorem rootLaw_eq_uniform (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    rootLaw rows repeats p slots = FiniteDistribution.uniform (RootTape rows repeats p slots) := by
  unfold rootLaw CutSamplerRefinement.tapeLaw
  simp only [UniformLinearImage.law_uniform]

theorem tapeLaw_eq_uniform (rows repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot),
      tapeLaw rows repeats p slots = FiniteDistribution.uniform (Tape rows repeats p slots) := by
  induction p with
  | refl n =>
      intro slots
      cases n with
      | zero => rfl
      | succ n => exact UniformLinearImage.law_uniform
  | @step n m i p ih =>
      intro slots
      change (rootLaw rows repeats (.step i p) slots).product
        ((tapeLaw rows repeats p (childSlots slots i)).product
          (FiniteProduct.law (fun j : RecursiveSampler.OffPath i =>
            FiniteDistribution.uniform (Arrays (childSlots slots j.val) rows)))) =
        FiniteDistribution.uniform
          (RootTape rows repeats (.step i p) slots ×
            (Tape rows repeats p (childSlots slots i) ×
              ((j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows)))
      rw [rootLaw_eq_uniform, ih, UniformLinearImage.law_uniform,
        uniform_product
          (R := Tape rows repeats p (childSlots slots i))
          (S := (j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows),
        uniform_product
          (R := RootTape rows repeats (.step i p) slots)
          (S := Tape rows repeats p (childSlots slots i) ×
            ((j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows))]

def stepComponent (i : Fin (branch n)) (Root Selected : Type)
    (Ordinary : RecursiveSampler.OffPath i → Type)
    [Fintype Root] [Fintype Selected] [∀ j, Fintype (Ordinary j)]
    (μ : FiniteDistribution Root) (ν : FiniteDistribution Selected)
    (P : (j : RecursiveSampler.OffPath i) → FiniteDistribution (Ordinary j)) :
    (k : WholeArraySampler.StepIndex i) → FiniteDistribution
      (WholeArraySampler.StepFactor Root Selected Ordinary k)
  | .inl _ => μ
  | .inr (.inl _) => ν
  | .inr (.inr j) => P j

theorem stepEquiv_law (i : Fin (branch n)) (Root Selected : Type)
    (Ordinary : RecursiveSampler.OffPath i → Type)
    [Fintype Root] [Fintype Selected] [∀ j, Fintype (Ordinary j)]
    (μ : FiniteDistribution Root) (ν : FiniteDistribution Selected)
    (P : (j : RecursiveSampler.OffPath i) → FiniteDistribution (Ordinary j)) :
    (μ.product (ν.product (FiniteProduct.law P))).pushforward
        (stepEquiv i Root Selected Ordinary) =
      FiniteProduct.law (stepComponent i Root Selected Ordinary μ ν P) := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change μ.weight (x (.inl ())) *
      (ν.weight (x (.inr (.inl ()))) *
        ∏ j : RecursiveSampler.OffPath i, (P j).weight (x (.inr (.inr j)))) =
    ∏ k : Unit ⊕ (Unit ⊕ RecursiveSampler.OffPath i),
      (stepComponent i Root Selected Ordinary μ ν P k).weight (x k)
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, stepComponent]

theorem collapseRoot_law (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    (rootLaw rows repeats p slots).pushforward (collapseRoot rows repeats p slots) =
      BucketSampler.recursiveTapeLaw (rows n) repeats p (LeafDomain slots) := by
  unfold rootLaw collapseRoot
  rw [CleanConditioning.pushforward_law]
  simp_rw [CutSamplerRefinement.collapse_tapeLaw]
  rfl

theorem terminal_law
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat) :
    (CutChildGrouping.rawLaw (C := Fin (rows (n + 1))) slots rows).pushforward
        (fun x => assembleArrays slots rows (CutChildGrouping.assemble slots rows x)) =
      FiniteDistribution.uniform (Arrays slots rows) := by
  rw [← FiniteDistribution.pushforward_comp
    (CutChildGrouping.rawLaw (C := Fin (rows (n + 1))) slots rows)
    (CutChildGrouping.assemble slots rows) (assembleArrays slots rows),
    CutChildGrouping.assemble_law]
  exact UniformLinearImage.uniform_pushforward_linearMap
    (R := F2)
    (A := CutChildGrouping.Assembled (C := Fin (rows (n + 1))) slots rows)
    (B := Arrays slots rows)
    (assembleArrays slots rows) (assembleArrays_surjective slots rows)

theorem collapse_tapeLaw (rows repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot),
      (tapeLaw rows repeats p slots).pushforward (collapse rows repeats p slots) =
        WholeArraySampler.tapeLaw rows repeats p slots := by
  induction p with
  | refl n =>
      intro slots
      cases n with
      | zero =>
          change (FiniteDistribution.uniform (Arrays slots rows)).pushforward
            (id : Arrays slots rows → Arrays slots rows) =
              FiniteDistribution.uniform (Arrays slots rows)
          exact FiniteDistribution.pushforward_id
            (FiniteDistribution.uniform (Arrays slots rows))
      | succ n => exact terminal_law slots rows
  | @step n m i p ih =>
      intro slots
      let R := WholeArraySampler.RootTape rows repeats (.step i p) slots
      let S := WholeArraySampler.Tape rows repeats p (childSlots slots i)
      let O := fun j : RecursiveSampler.OffPath i => Arrays (childSlots slots j.val) rows
      let : (k : WholeArraySampler.StepIndex i) → Fintype
          (WholeArraySampler.StepFactor R S O k) :=
        fun k => WholeArraySampler.stepFactorFintype R S O k
      let μ : FiniteDistribution R :=
        BucketSampler.recursiveTapeLaw (rows (n + 1)) repeats (.step i p) (LeafDomain slots)
      let ν : FiniteDistribution S := WholeArraySampler.tapeLaw rows repeats p (childSlots slots i)
      let P : (j : RecursiveSampler.OffPath i) → FiniteDistribution (O j) :=
        fun j => FiniteDistribution.uniform (Arrays (childSlots slots j.val) rows)
      let f : Tape rows repeats (.step i p) slots → R × (S × ((j : RecursiveSampler.OffPath i) → O j)) :=
        fun x => (collapseRoot rows repeats (.step i p) slots x.1,
          collapse rows repeats p (childSlots slots i) x.2.1, x.2.2)
      have hmap : (tapeLaw rows repeats (.step i p) slots).pushforward f =
          μ.product (ν.product (FiniteProduct.law P)) := by
        change ((rootLaw rows repeats (.step i p) slots).product
          ((tapeLaw rows repeats p (childSlots slots i)).product (FiniteProduct.law P))).pushforward
            (fun x => (collapseRoot rows repeats (.step i p) slots x.1,
              (fun y => (collapse rows repeats p (childSlots slots i) y.1, id y.2)) x.2)) = _
        rw [FiniteDistribution.product_pushforward
          (rootLaw rows repeats (.step i p) slots)
          ((tapeLaw rows repeats p (childSlots slots i)).product (FiniteProduct.law P))
          (collapseRoot rows repeats (.step i p) slots)
          (fun y => (collapse rows repeats p (childSlots slots i) y.1, id y.2))]
        rw [FiniteDistribution.product_pushforward
          (tapeLaw rows repeats p (childSlots slots i)) (FiniteProduct.law P)
          (collapse rows repeats p (childSlots slots i)) id,
          collapseRoot_law, ih, FiniteDistribution.pushforward_id (FiniteProduct.law P)]
      change (tapeLaw rows repeats (.step i p) slots).pushforward
        (fun x => stepEquiv i R S O (f x)) = _
      rw [← FiniteDistribution.pushforward_comp
        (tapeLaw rows repeats (.step i p) slots) f (stepEquiv i R S O), hmap]
      exact stepEquiv_law i R S O μ ν P

def evaluate (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (x : Tape rows repeats p slots) : Arrays slots rows :=
  WholeArraySampler.evaluate rows repeats p slots (collapse rows repeats p slots x)

def law (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Arrays slots rows) :=
  (tapeLaw rows repeats p slots).pushforward (evaluate rows repeats p slots)

theorem evaluate_law (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    law rows repeats p slots = WholeArraySampler.law rows repeats p slots := by
  change (tapeLaw rows repeats p slots).pushforward
    (fun x => WholeArraySampler.evaluate rows repeats p slots (collapse rows repeats p slots x)) = _
  rw [← FiniteDistribution.pushforward_comp
    (tapeLaw rows repeats p slots) (collapse rows repeats p slots)
    (WholeArraySampler.evaluate rows repeats p slots), collapse_tapeLaw]
  rfl

end

end PerfectCompleteness.WholeCutSampler

end

end OAI
