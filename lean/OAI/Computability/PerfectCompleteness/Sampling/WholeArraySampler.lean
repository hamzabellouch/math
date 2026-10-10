import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalArrays
import OAI.Computability.PerfectCompleteness.Sampling.BucketSampler
import OAI.Computability.UniqueGames.Games.FinishBoundsLemmas

namespace OAI

section

namespace PerfectCompleteness.WholeArraySampler

open TreeSourceSpaces HierarchicalArrays DescendantSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

abbrev StepIndex (i : Fin (branch n)) :=
  Unit ⊕ (Unit ⊕ RecursiveSampler.OffPath i)

def StepFactor {i : Fin (branch n)} (Root Selected : Type)
    (Ordinary : RecursiveSampler.OffPath i → Type) : StepIndex i → Type
  | .inl _ => Root
  | .inr (.inl _) => Selected
  | .inr (.inr j) => Ordinary j

instance stepFactorFintype {i : Fin (branch n)} (Root Selected : Type)
    (Ordinary : RecursiveSampler.OffPath i → Type)
    [Fintype Root] [Fintype Selected] [∀ j, Fintype (Ordinary j)]
    (k : StepIndex i) : Fintype (StepFactor Root Selected Ordinary k) := by
  rcases k with _ | (_ | j) <;> dsimp only [StepFactor] <;> infer_instance

abbrev StepTape {i : Fin (branch n)} (Root Selected : Type)
    (Ordinary : RecursiveSampler.OffPath i → Type) :=
  (k : StepIndex i) → StepFactor Root Selected Ordinary k

noncomputable instance spaceFintype
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (H slots) := Fintype.ofFinite _

abbrev RootTape (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :=
  BucketSampler.RecursiveTape (rows n) repeats p (LeafDomain slots)

def Tape (rows repeats : Nat → Nat) :
    {n m : Nat} → Path branch n m →
      (RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) → Type
  | _, _, .refl _, slots => Arrays slots rows
  | _, _, .step i p, slots =>
      StepTape (i := i) (RootTape rows repeats (.step i p) slots)
        (Tape rows repeats p (childSlots slots i))
        (fun j => Arrays (childSlots slots j.val) rows)

@[instance_reducible] def tapeFintypeAux (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) →
      (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) →
        Fintype (Tape rows repeats p slots)
  | _, _, .refl _, slots => inferInstanceAs (Fintype (Arrays slots rows))
  | _, _, .step i p, slots =>
      letI : Fintype (Tape rows repeats p (childSlots slots i)) :=
        tapeFintypeAux rows repeats p (childSlots slots i)
      letI : (k : StepIndex i) → Fintype
          (StepFactor (RootTape rows repeats (.step i p) slots)
            (Tape rows repeats p (childSlots slots i))
            (fun j => Arrays (childSlots slots j.val) rows) k) :=
        fun k => stepFactorFintype _ _ _ k
      inferInstanceAs (Fintype
        (StepTape (i := i) (RootTape rows repeats (.step i p) slots)
          (Tape rows repeats p (childSlots slots i))
          (fun j => Arrays (childSlots slots j.val) rows)))

instance tapeFintype (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (Tape rows repeats p slots) := tapeFintypeAux rows repeats p slots

def zeroTape (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) →
      (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) →
        Tape rows repeats p slots
  | _, _, .refl _, _ => fun _ _ => 0
  | _, _, .step i p, slots => fun k =>
      match k with
      | .inl _ => fun _ =>
          RecursiveSampler.zeroTape F2 repeats (.step i p) (LeafDomain slots)
      | .inr (.inl _) => zeroTape rows repeats p (childSlots slots i)
      | .inr (.inr _) => fun _ _ => 0

instance tapeNonempty (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    Nonempty (Tape rows repeats p slots) := ⟨zeroTape rows repeats p slots⟩

def leafTapeEquivUnit (rows repeats : Nat → Nat)
    (slots : RecursiveSpaces.Slots branch 0 → Fin t → MixedSupport.Slot) :
    Tape rows repeats (.refl 0) slots ≃ Unit where
  toFun _ := ()
  invFun _ := fun node => nomatch node
  left_inv ω := by
    funext node
    exact nomatch node
  right_inv u := by cases u; rfl

def assemble (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat) (root : Fin (rows (n + 1)) → H slots)
    (children : ∀ j, Arrays (childSlots slots j) rows) : Arrays slots rows
  | .inl _ => root
  | .inr (j, node) => children j node

def childrenAt (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat) (i : Fin (branch n))
    (selected : Arrays (childSlots slots i) rows)
    (ordinary : ∀ j : RecursiveSampler.OffPath i, Arrays (childSlots slots j.val) rows)
    (j : Fin (branch n)) : Arrays (childSlots slots j) rows :=
  if h : j = i then h.symm ▸ selected else ordinary ⟨j, h⟩

@[simp] theorem childrenAt_selected
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat) (i : Fin (branch n))
    (selected : Arrays (childSlots slots i) rows)
    (ordinary : ∀ j : RecursiveSampler.OffPath i, Arrays (childSlots slots j.val) rows) :
    childrenAt slots rows i selected ordinary i = selected := by simp [childrenAt]

@[simp] theorem childrenAt_ordinary
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat) (i : Fin (branch n))
    (selected : Arrays (childSlots slots i) rows)
    (ordinary : ∀ j : RecursiveSampler.OffPath i, Arrays (childSlots slots j.val) rows)
    (j : RecursiveSampler.OffPath i) :
    childrenAt slots rows i selected ordinary j.val = ordinary j := by
  simp [childrenAt, j.property]

def evaluate (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) →
      (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) →
        Tape rows repeats p slots → Arrays slots rows
  | _, _, .refl _, _, ω => ω
  | n + 1, _, .step i p, slots, ω =>
      assemble slots rows
        (BucketSampler.recursiveEvaluate (rows (n + 1)) repeats (.step i p)
          (LeafDomain slots) (ω (.inl ())))
        (childrenAt slots rows i
          (evaluate rows repeats p (childSlots slots i) (ω (.inr (.inl ()))))
          (fun j => ω (.inr (.inr j))))

@[simp] theorem evaluate_refl (rows repeats : Nat → Nat)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats (.refl n) slots) :
    evaluate rows repeats (.refl n) slots ω = ω := rfl

@[simp] theorem evaluate_root (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats (.step i p) slots) :
    evaluate rows repeats (.step i p) slots ω (.inl ()) =
      BucketSampler.recursiveEvaluate (rows (n + 1)) repeats (.step i p)
        (LeafDomain slots) (ω (.inl ())) := rfl

@[simp] theorem evaluate_selected (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats (.step i p) slots) (node : Nodes branch n) :
    evaluate rows repeats (.step i p) slots ω (.inr (i, node)) =
      evaluate rows repeats p (childSlots slots i) (ω (.inr (.inl ()))) node := by
  exact congrFun (childrenAt_selected slots rows i
    (evaluate rows repeats p (childSlots slots i) (ω (.inr (.inl ()))))
    (fun j => ω (.inr (.inr j)))) node

@[simp] theorem evaluate_ordinary (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats (.step i p) slots) (j : RecursiveSampler.OffPath i)
    (node : Nodes branch n) :
    evaluate rows repeats (.step i p) slots ω (.inr (j.val, node)) =
      ω (.inr (.inr j)) node := by
  exact congrFun (childrenAt_ordinary slots rows i
    (evaluate rows repeats p (childSlots slots i) (ω (.inr (.inl ()))))
    (fun j => ω (.inr (.inr j))) j) node

def tapeLaw (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) →
      (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) →
        FiniteDistribution (Tape rows repeats p slots)
  | _, _, .refl _, slots => FiniteDistribution.uniform (Arrays slots rows)
  | n + 1, _, .step i p, slots => by
      letI : (k : StepIndex i) → Fintype
          (StepFactor (RootTape rows repeats (.step i p) slots)
            (Tape rows repeats p (childSlots slots i))
            (fun j => Arrays (childSlots slots j.val) rows) k) :=
        fun k => stepFactorFintype _ _ _ k
      exact FiniteProduct.law
        (Ω := fun k : StepIndex i => StepFactor (RootTape rows repeats (.step i p) slots)
          (Tape rows repeats p (childSlots slots i))
          (fun j => Arrays (childSlots slots j.val) rows) k)
        (fun k : StepIndex i => match k with
          | .inl _ => BucketSampler.recursiveTapeLaw (rows (n + 1)) repeats (.step i p)
              (LeafDomain slots)
          | .inr (.inl _) => tapeLaw rows repeats p (childSlots slots i)
          | .inr (.inr j) => FiniteDistribution.uniform (Arrays (childSlots slots j.val) rows))

def componentLaw (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    (k : StepIndex i) → FiniteDistribution
      (StepFactor (RootTape rows repeats (.step i p) slots)
        (Tape rows repeats p (childSlots slots i))
        (fun j => Arrays (childSlots slots j.val) rows) k)
  | .inl _ => BucketSampler.recursiveTapeLaw (rows (n + 1)) repeats (.step i p)
      (LeafDomain slots)
  | .inr (.inl _) => tapeLaw rows repeats p (childSlots slots i)
  | .inr (.inr j) => FiniteDistribution.uniform (Arrays (childSlots slots j.val) rows)

theorem component_marginal (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (k : StepIndex i) :
    (tapeLaw rows repeats (.step i p) slots).pushforward (fun ω => ω k) =
      componentLaw rows repeats i p slots k := by
  let : (k : StepIndex i) → Fintype
      (StepFactor (RootTape rows repeats (.step i p) slots)
        (Tape rows repeats p (childSlots slots i))
        (fun j => Arrays (childSlots slots j.val) rows) k) :=
    fun k => stepFactorFintype _ _ _ k
  exact FiniteProduct.eval_pushforward (componentLaw rows repeats i p slots) k

theorem component_image (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (k : StepIndex i) {Y : Type*} [Fintype Y]
    (f : StepFactor (RootTape rows repeats (.step i p) slots)
      (Tape rows repeats p (childSlots slots i))
      (fun j => Arrays (childSlots slots j.val) rows) k → Y) :
    (tapeLaw rows repeats (.step i p) slots).pushforward (fun ω => f (ω k)) =
      (componentLaw rows repeats i p slots k).pushforward f := by
  rw [← FiniteDistribution.pushforward_comp
    (tapeLaw rows repeats (.step i p) slots) (fun ω => ω k) f,
    component_marginal]

theorem components_independent (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (k l : StepIndex i) (hne : k ≠ l)
    (f : StepFactor (RootTape rows repeats (.step i p) slots)
      (Tape rows repeats p (childSlots slots i))
      (fun j => Arrays (childSlots slots j.val) rows) k → ℝ)
    (g : StepFactor (RootTape rows repeats (.step i p) slots)
      (Tape rows repeats p (childSlots slots i))
      (fun j => Arrays (childSlots slots j.val) rows) l → ℝ) :
    (tapeLaw rows repeats (.step i p) slots).expectation (fun ω => f (ω k) * g (ω l)) =
      (componentLaw rows repeats i p slots k).expectation f *
        (componentLaw rows repeats i p slots l).expectation g := by
  let : (k : StepIndex i) → Fintype
      (StepFactor (RootTape rows repeats (.step i p) slots)
        (Tape rows repeats p (childSlots slots i))
        (fun j => Arrays (childSlots slots j.val) rows) k) :=
    fun k => stepFactorFintype _ _ _ k
  exact FiniteProduct.expectation_eval_mul (componentLaw rows repeats i p slots) k l hne f g

theorem components_expectation_product (rows repeats : Nat → Nat)
    (i : Fin (branch n)) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (f : (k : StepIndex i) → StepFactor (RootTape rows repeats (.step i p) slots)
      (Tape rows repeats p (childSlots slots i))
      (fun j => Arrays (childSlots slots j.val) rows) k → ℝ) :
    (tapeLaw rows repeats (.step i p) slots).expectation (fun ω => ∏ k, f k (ω k)) =
      ∏ k, (componentLaw rows repeats i p slots k).expectation (f k) := by
  let : (k : StepIndex i) → Fintype
      (StepFactor (RootTape rows repeats (.step i p) slots)
        (Tape rows repeats p (childSlots slots i))
        (fun j => Arrays (childSlots slots j.val) rows) k) :=
    fun k => stepFactorFintype _ _ _ k
  exact FiniteProduct.expectation_product (componentLaw rows repeats i p slots) f

def law (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Arrays slots rows) :=
  (tapeLaw rows repeats p slots).pushforward (evaluate rows repeats p slots)

theorem probability_law (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (event : Arrays slots rows → Bool) :
    (law rows repeats p slots).probability event =
      (tapeLaw rows repeats p slots).probability
        (fun ω => event (evaluate rows repeats p slots ω)) :=
  FiniteDistribution.probability_pushforward _ _ _

theorem root_array_marginal (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    (tapeLaw rows repeats (.step i p) slots).pushforward
        (fun ω => evaluate rows repeats (.step i p) slots ω (.inl ())) =
      BucketSampler.law (rows (n + 1))
        (RecursiveSampler.tapeLaw F2 repeats (.step i p) (LeafDomain slots))
        (RecursiveSampler.evaluate F2 repeats (.step i p) (LeafDomain slots)) :=
  component_image rows repeats i p slots (.inl ())
    (BucketSampler.recursiveEvaluate (rows (n + 1)) repeats (.step i p) (LeafDomain slots))

theorem selected_arrays_marginal (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    (tapeLaw rows repeats (.step i p) slots).pushforward
        (fun ω node => evaluate rows repeats (.step i p) slots ω (.inr (i, node))) =
      law rows repeats p (childSlots slots i) := by
  simp only [evaluate_selected]
  exact component_image rows repeats i p slots (.inr (.inl ()))
    (evaluate rows repeats p (childSlots slots i))

theorem uniform_arrays_eq_product
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat) :
    FiniteDistribution.uniform (Arrays slots rows) =
      FiniteProduct.law (fun node : Nodes branch n =>
        FiniteDistribution.uniform (Fin (rows (Nodes.height node)) → H (nodeSlots slots node))) :=
  UniformLinearImage.law_uniform.symm

theorem uniform_arrays_node
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat) (node : Nodes branch n) :
    (FiniteDistribution.uniform (Arrays slots rows)).pushforward (fun arrays => arrays node) =
      FiniteDistribution.uniform (Fin (rows (Nodes.height node)) → H (nodeSlots slots node)) := by
  rw [uniform_arrays_eq_product]
  exact FiniteProduct.eval_pushforward _ node

theorem uniform_arrays_expectation_product
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat)
    (f : (node : Nodes branch n) →
      (Fin (rows (Nodes.height node)) → H (nodeSlots slots node)) → ℝ) :
    (FiniteDistribution.uniform (Arrays slots rows)).expectation
        (fun arrays => ∏ node, f node (arrays node)) =
      ∏ node, (FiniteDistribution.uniform
        (Fin (rows (Nodes.height node)) → H (nodeSlots slots node))).expectation (f node) := by
  rw [uniform_arrays_eq_product]
  exact FiniteProduct.expectation_product _ f

theorem ordinary_node_marginal (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (j : RecursiveSampler.OffPath i) (node : Nodes branch n) :
    (tapeLaw rows repeats (.step i p) slots).pushforward
        (fun ω => evaluate rows repeats (.step i p) slots ω (.inr (j.val, node))) =
      FiniteDistribution.uniform
        (Fin (rows (Nodes.height node)) → H (nodeSlots (childSlots slots j.val) node)) := by
  have hfun :
      (fun ω : Tape rows repeats (.step i p) slots =>
        (evaluate rows repeats (.step i p) slots ω (.inr (j.val, node)) :
          Fin (rows (Nodes.height node)) → H (nodeSlots (childSlots slots j.val) node))) =
      (fun ω : Tape rows repeats (.step i p) slots => ω (.inr (.inr j)) node) := by
    funext ω
    exact evaluate_ordinary rows repeats i p slots ω j node
  exact (congrArg
    (fun f : Tape rows repeats (.step i p) slots →
        (Fin (rows (Nodes.height node)) → H (nodeSlots (childSlots slots j.val) node)) =>
      (tapeLaw rows repeats (.step i p) slots).pushforward f) hfun).trans
    ((component_image rows repeats i p slots (.inr (.inr j))
      (fun arrays => arrays node)).trans (uniform_arrays_node (childSlots slots j.val) rows node))

end

end PerfectCompleteness.WholeArraySampler

end

end OAI
