import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionOrderLemmas
import OAI.Computability.PerfectCompleteness.Sampling.WholeArrayProductLaw

namespace OAI

section

namespace PerfectCompleteness.OriginalBelowCut

open TreeSourceSpaces HierarchicalArrays DescendantSpaces WholeArraySampler
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def below (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats (.step chosen q) slots) :
    (child : Fin (branch n)) → Arrays (childSlots slots child) rows :=
  fun child node => WholeArraySampler.evaluate rows repeats (.step chosen q) slots ω
    (.inr (child, node))

@[simp] theorem below_selected (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats (.step chosen q) slots) :
    below rows repeats chosen q slots ω chosen =
      WholeArraySampler.evaluate rows repeats q (childSlots slots chosen)
        (ω (.inr (.inl ()))) := by
  funext node
  exact WholeArraySampler.evaluate_selected rows repeats chosen q slots ω node

@[simp] theorem below_ordinary (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats (.step chosen q) slots) (j : RecursiveSampler.OffPath chosen) :
    below rows repeats chosen q slots ω j.val = ω (.inr (.inr j)) := by
  funext node
  exact WholeArraySampler.evaluate_ordinary rows repeats chosen q slots ω j node

def stepObservable (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (f : (child : Fin (branch n)) → Arrays (childSlots slots child) rows → ℝ) :
    (k : StepIndex chosen) →
      StepFactor (RootTape rows repeats (.step chosen q) slots)
        (Tape rows repeats q (childSlots slots chosen))
        (fun j => Arrays (childSlots slots j.val) rows) k → ℝ
  | .inl _, _ => 1
  | .inr (.inl _), ω =>
      f chosen (WholeArraySampler.evaluate rows repeats q (childSlots slots chosen) ω)
  | .inr (.inr j), arrays => f j.val arrays

theorem prod_below (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (f : (child : Fin (branch n)) → Arrays (childSlots slots child) rows → ℝ)
    (ω : Tape rows repeats (.step chosen q) slots) :
    (∏ child, f child (below rows repeats chosen q slots ω child)) =
      ∏ k : StepIndex chosen, stepObservable rows repeats chosen q slots f k (ω k) := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (fun child => f child (below rows repeats chosen q slots ω child)) chosen,
    WholeArrayProductLaw.prod_stepIndex chosen]
  simp only [stepObservable, one_mul, below_selected, below_ordinary]

theorem expectation_product (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (f : (child : Fin (branch n)) → Arrays (childSlots slots child) rows → ℝ) :
    (WholeArraySampler.tapeLaw rows repeats (.step chosen q) slots).expectation
        (fun ω => ∏ child, f child (below rows repeats chosen q slots ω child)) =
      ∏ child, (ChildBlockMixture.component
        (fun j => WholeArraySampler.law rows repeats q (childSlots slots j))
        chosen child).expectation (f child) := by
  calc
    _ = (WholeArraySampler.tapeLaw rows repeats (.step chosen q) slots).expectation
        (fun ω => ∏ k : StepIndex chosen,
          stepObservable rows repeats chosen q slots f k (ω k)) :=
      FiniteDistribution.expectation_congr _ (prod_below rows repeats chosen q slots f)
    _ = ∏ k : StepIndex chosen, (componentLaw rows repeats chosen q slots k).expectation
        (stepObservable rows repeats chosen q slots f k) :=
      WholeArraySampler.components_expectation_product rows repeats chosen q slots _
    _ = _ := by
      let Q : (child : Fin (branch n)) →
          FiniteDistribution (Arrays (childSlots slots child) rows) :=
        fun child => WholeArraySampler.law rows repeats q (childSlots slots child)
      let L : StepIndex chosen → ℝ := fun k =>
        (componentLaw rows repeats chosen q slots k).expectation
          (stepObservable rows repeats chosen q slots f k)
      let R : Fin (branch n) → ℝ := fun child =>
        (ChildBlockMixture.component Q chosen child).expectation (f child)
      change (∏ k, L k) = ∏ child, R child
      have hroot : L (.inl ()) = 1 :=
        SmallBias.expectation_const _ 1
      have hselected : L (.inr (.inl ())) = R chosen := by
        change (WholeArraySampler.tapeLaw rows repeats q (childSlots slots chosen)).expectation
          (fun ω => f chosen (WholeArraySampler.evaluate rows repeats q
            (childSlots slots chosen) ω)) =
          (ChildBlockMixture.component Q chosen chosen).expectation (f chosen)
        simp only [ChildBlockMixture.component]
        exact (FiniteDistribution.expectation_pushforward
          (WholeArraySampler.tapeLaw rows repeats q (childSlots slots chosen))
          (WholeArraySampler.evaluate rows repeats q (childSlots slots chosen))
          (f chosen)).symm
      have hordinary (j : RecursiveSampler.OffPath chosen) :
          L (.inr (.inr j)) = R j.val := by
        change (FiniteDistribution.uniform (Arrays (childSlots slots j.val) rows)).expectation
          (f j.val) = (ChildBlockMixture.component Q chosen j.val).expectation (f j.val)
        simp only [ChildBlockMixture.component, dite_eq_right (Ne.symm j.property)]
      rw [WholeArrayProductLaw.prod_stepIndex chosen, hroot, one_mul, hselected,
        Fintype.prod_eq_mul_prod_subtype_ne R chosen]
      exact congrArg (fun z : ℝ => R chosen * z)
        (Finset.prod_congr rfl (fun j _ => hordinary j))

theorem below_pushforward (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    (WholeArraySampler.tapeLaw rows repeats (.step chosen q) slots).pushforward
        (below rows repeats chosen q slots) =
      FiniteProduct.law (ChildBlockMixture.component
        (fun child => WholeArraySampler.law rows repeats q (childSlots slots child)) chosen) := by
  apply WholeArrayProductLaw.eq_law_of_expectation_product
  intro f
  rw [FiniteDistribution.expectation_pushforward]
  exact expectation_product rows repeats chosen q slots f

end

end PerfectCompleteness.OriginalBelowCut

end

end OAI
