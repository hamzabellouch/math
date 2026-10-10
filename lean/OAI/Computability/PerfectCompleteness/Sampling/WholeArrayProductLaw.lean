import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import OAI.Computability.PerfectCompleteness.Sampling.WholeArraySampler

namespace OAI

section

namespace PerfectCompleteness.WholeArrayProductLaw

open TreeSourceSpaces HierarchicalArrays DescendantSpaces WholeArraySampler
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

abbrev NodeArray
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat) (node : Nodes branch n) :=
  Fin (rows (Nodes.height node)) → H (nodeSlots slots node)

def nodeLaw (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (node : Nodes branch n) : FiniteDistribution (NodeArray slots rows node) :=
  (WholeArraySampler.tapeLaw rows repeats p slots).pushforward
    (fun ω => WholeArraySampler.evaluate rows repeats p slots ω node)

theorem nodeLaw_refl (rows repeats : Nat → Nat)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (node : Nodes branch n) :
    nodeLaw rows repeats (.refl n) slots node =
      FiniteDistribution.uniform (NodeArray slots rows node) :=
  WholeArraySampler.uniform_arrays_node slots rows node

theorem nodeLaw_root (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    nodeLaw rows repeats (.step i p) slots (.inl ()) =
      BucketSampler.law (rows (n + 1))
        (RecursiveSampler.tapeLaw F2 repeats (.step i p) (LeafDomain slots))
        (RecursiveSampler.evaluate F2 repeats (.step i p) (LeafDomain slots)) :=
  WholeArraySampler.root_array_marginal rows repeats i p slots

theorem nodeLaw_selected (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (node : Nodes branch n) :
    nodeLaw rows repeats (.step i p) slots (.inr (i, node)) =
      nodeLaw rows repeats p (childSlots slots i) node := by
  unfold nodeLaw
  simp only [WholeArraySampler.evaluate_selected]
  exact WholeArraySampler.component_image rows repeats i p slots (.inr (.inl ()))
    (fun ω => WholeArraySampler.evaluate rows repeats p (childSlots slots i) ω node)

theorem nodeLaw_ordinary (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (j : RecursiveSampler.OffPath i) (node : Nodes branch n) :
    nodeLaw rows repeats (.step i p) slots (.inr (j.val, node)) =
      FiniteDistribution.uniform (NodeArray (childSlots slots j.val) rows node) :=
  WholeArraySampler.ordinary_node_marginal rows repeats i p slots j node

theorem prod_nodes (i : Fin (branch n)) (f : Nodes branch (n + 1) → ℝ) :
    (∏ node, f node) = f (.inl ()) *
      ((∏ node : Nodes branch n, f (.inr (i, node))) *
        ∏ j : RecursiveSampler.OffPath i, ∏ node : Nodes branch n, f (.inr (j.val, node))) := by
  let g : Unit ⊕ (Fin (branch n) × Nodes branch n) → ℝ := f
  change (∏ node : Unit ⊕ (Fin (branch n) × Nodes branch n), g node) = g (.inl ()) *
    ((∏ node : Nodes branch n, g (.inr (i, node))) *
      ∏ j : RecursiveSampler.OffPath i, ∏ node : Nodes branch n, g (.inr (j.val, node)))
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp only [Fintype.prod_unique]
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (fun j : Fin (branch n) => ∏ node : Nodes branch n, g (.inr (j, node))) i]

theorem prod_stepIndex (i : Fin (branch n)) (f : StepIndex i → ℝ) :
    (∏ k, f k) = f (.inl ()) *
      (f (.inr (.inl ())) * ∏ j : RecursiveSampler.OffPath i, f (.inr (.inr j))) := by
  change (∏ k : Unit ⊕ (Unit ⊕ RecursiveSampler.OffPath i), f k) = _
  simp only [Fintype.prod_sum_type, Fintype.prod_unique]

def stepObservable (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (f : (node : Nodes branch (n + 1)) → NodeArray slots rows node → ℝ) :
    (k : StepIndex i) → StepFactor (RootTape rows repeats (.step i p) slots)
      (Tape rows repeats p (childSlots slots i))
      (fun j => Arrays (childSlots slots j.val) rows) k → ℝ
  | .inl _, ω => f (.inl ())
      (BucketSampler.recursiveEvaluate (rows (n + 1)) repeats (.step i p) (LeafDomain slots) ω)
  | .inr (.inl _), ω =>
      ∏ node : Nodes branch n, f (.inr (i, node))
        (WholeArraySampler.evaluate rows repeats p (childSlots slots i) ω node)
  | .inr (.inr j), arrays =>
      ∏ node : Nodes branch n, f (.inr (j.val, node)) (arrays node)

theorem prod_evaluate_step (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (f : (node : Nodes branch (n + 1)) → NodeArray slots rows node → ℝ)
    (ω : Tape rows repeats (.step i p) slots) :
    (∏ node, f node (WholeArraySampler.evaluate rows repeats (.step i p) slots ω node)) =
      ∏ k : StepIndex i, stepObservable rows repeats i p slots f k (ω k) := by
  rw [prod_nodes i, prod_stepIndex i]
  simp only [WholeArraySampler.evaluate_root, WholeArraySampler.evaluate_selected,
    WholeArraySampler.evaluate_ordinary, stepObservable]

theorem tape_expectation_product (rows repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
      (f : (node : Nodes branch n) → NodeArray slots rows node → ℝ),
      (WholeArraySampler.tapeLaw rows repeats p slots).expectation
          (fun ω => ∏ node, f node (WholeArraySampler.evaluate rows repeats p slots ω node)) =
        ∏ node, (nodeLaw rows repeats p slots node).expectation (f node) := by
  induction p with
  | refl n =>
      intro slots f
      calc
        _ = (FiniteDistribution.uniform (Arrays slots rows)).expectation
            (fun arrays => ∏ node, f node (arrays node)) := rfl
        _ = ∏ node, (FiniteDistribution.uniform
            (Fin (rows (Nodes.height node)) → H (nodeSlots slots node))).expectation (f node) :=
          WholeArraySampler.uniform_arrays_expectation_product slots rows f
        _ = _ := by
          apply Finset.prod_congr rfl
          intro node _
          exact congrArg
            (fun μ : FiniteDistribution (NodeArray slots rows node) => μ.expectation (f node))
            (nodeLaw_refl rows repeats slots node).symm
  | @step n m i p ih =>
      intro slots f
      calc
        _ = (WholeArraySampler.tapeLaw rows repeats (.step i p) slots).expectation
            (fun ω => ∏ k : StepIndex i, stepObservable rows repeats i p slots f k (ω k)) :=
          FiniteDistribution.expectation_congr _ (prod_evaluate_step rows repeats i p slots f)
        _ = ∏ k : StepIndex i, (componentLaw rows repeats i p slots k).expectation
            (stepObservable rows repeats i p slots f k) :=
          WholeArraySampler.components_expectation_product rows repeats i p slots _
        _ = _ := by
          let L : StepIndex i → ℝ := fun k =>
            (componentLaw rows repeats i p slots k).expectation
              (stepObservable rows repeats i p slots f k)
          let R : Nodes branch (n + 1) → ℝ := fun node =>
            (nodeLaw rows repeats (.step i p) slots node).expectation (f node)
          have hroot : L (.inl ()) = R (.inl ()) := by
            calc
              _ = (BucketSampler.law (rows (n + 1))
                  (RecursiveSampler.tapeLaw F2 repeats (.step i p) (LeafDomain slots))
                  (RecursiveSampler.evaluate F2 repeats (.step i p) (LeafDomain slots))).expectation
                    (f (.inl ())) :=
                (FiniteDistribution.expectation_pushforward
                  (BucketSampler.recursiveTapeLaw (rows (n + 1)) repeats (.step i p) (LeafDomain slots))
                  (BucketSampler.recursiveEvaluate (rows (n + 1)) repeats (.step i p) (LeafDomain slots))
                  (f (.inl ()))).symm
              _ = _ := congrArg
                (fun μ : FiniteDistribution (NodeArray slots rows (.inl ())) =>
                  μ.expectation (f (.inl ()))) (nodeLaw_root rows repeats i p slots).symm
          have hselected : L (.inr (.inl ())) =
              ∏ node : Nodes branch n, R (.inr (i, node)) := by
            calc
              _ = ∏ node : Nodes branch n,
                  (nodeLaw rows repeats p (childSlots slots i) node).expectation
                    (fun a : NodeArray (childSlots slots i) rows node => f (.inr (i, node)) a) :=
                ih (childSlots slots i) (fun node a => f (.inr (i, node)) a)
              _ = _ := by
                apply Finset.prod_congr rfl
                intro node _
                exact congrArg
                  (fun μ : FiniteDistribution (NodeArray (childSlots slots i) rows node) =>
                    μ.expectation (fun a => f (.inr (i, node)) a))
                  (nodeLaw_selected rows repeats i p slots node).symm
          have hordinary (j : RecursiveSampler.OffPath i) : L (.inr (.inr j)) =
              ∏ node : Nodes branch n, R (.inr (j.val, node)) := by
            calc
              _ = ∏ node : Nodes branch n,
                  (FiniteDistribution.uniform
                    (NodeArray (childSlots slots j.val) rows node)).expectation
                    (fun a : NodeArray (childSlots slots j.val) rows node => f (.inr (j.val, node)) a) :=
                WholeArraySampler.uniform_arrays_expectation_product
                  (childSlots slots j.val) rows (fun node a => f (.inr (j.val, node)) a)
              _ = _ := by
                apply Finset.prod_congr rfl
                intro node _
                exact congrArg
                  (fun μ : FiniteDistribution (NodeArray (childSlots slots j.val) rows node) =>
                    μ.expectation (fun a => f (.inr (j.val, node)) a))
                  (nodeLaw_ordinary rows repeats i p slots j node).symm
          have hordinaryProd : (∏ j : RecursiveSampler.OffPath i, L (.inr (.inr j))) =
              ∏ j : RecursiveSampler.OffPath i, ∏ node : Nodes branch n, R (.inr (j.val, node)) :=
            Finset.prod_congr rfl (fun j _ => hordinary j)
          exact (prod_stepIndex i L).trans
            ((congrArg₂ (fun a b : ℝ => a * b) hroot
              (congrArg₂ (fun a b : ℝ => a * b) hselected hordinaryProd)).trans
                (prod_nodes i R).symm)

theorem eq_law_of_expectation_product {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (μ : FiniteDistribution (∀ i, Ω i)) (P : ∀ i, FiniteDistribution (Ω i))
    (h : ∀ f : ∀ i, Ω i → ℝ,
      μ.expectation (fun x => ∏ i, f i (x i)) = ∏ i, (P i).expectation (f i)) :
    μ = FiniteProduct.law P := by
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  calc
    μ.weight y = μ.expectation (fun x => if x = y then 1 else 0) := by
      simp [FiniteDistribution.expectation, mul_ite]
    _ = μ.expectation (fun x => ∏ i, if x i = y i then 1 else 0) := by
      apply FiniteDistribution.expectation_congr
      intro x
      simp only [Fintype.prod_boole, funext_iff]
    _ = ∏ i, (P i).expectation (fun a => if a = y i then 1 else 0) :=
      h (fun i a => if a = y i then (1 : ℝ) else 0)
    _ = (FiniteProduct.law P).weight y := by
      simp [FiniteProduct.law, FiniteDistribution.expectation, mul_ite]

theorem law_eq_product (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    WholeArraySampler.law rows repeats p slots =
      FiniteProduct.law (nodeLaw rows repeats p slots) := by
  apply eq_law_of_expectation_product
  intro f
  rw [WholeArraySampler.law, FiniteDistribution.expectation_pushforward]
  exact tape_expectation_product rows repeats p slots f

theorem node_marginal (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (node : Nodes branch n) :
    (WholeArraySampler.law rows repeats p slots).pushforward (fun arrays => arrays node) =
      nodeLaw rows repeats p slots node := by
  rw [law_eq_product]
  exact FiniteProduct.eval_pushforward _ node

theorem law_eq_product_marginals (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    WholeArraySampler.law rows repeats p slots =
      FiniteProduct.law (fun node : Nodes branch n =>
        (WholeArraySampler.law rows repeats p slots).pushforward (fun arrays => arrays node)) := by
  simp only [node_marginal]
  exact law_eq_product rows repeats p slots

end

end PerfectCompleteness.WholeArrayProductLaw

end

end OAI
