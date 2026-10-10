import OAI.Computability.PerfectCompleteness.Construction.CutChildGrouping
import OAI.Computability.PerfectCompleteness.Construction.OriginalChildScalarAssemblyLemmas
import OAI.Computability.PerfectCompleteness.Construction.OriginalChildScalars
import OAI.Computability.PerfectCompleteness.Foundations.OriginalBelowCut
import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerReplayTransportLemmas

namespace OAI

section

namespace PerfectCompleteness.OriginalChildBlocks

open PointwiseSpaces RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalChildScalars
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

private theorem uniform_product {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    (FiniteDistribution.uniform A).product (FiniteDistribution.uniform B) =
      FiniteDistribution.uniform (A × B) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  simp only [FiniteDistribution.product, FiniteDistribution.uniform,
    Fintype.card_prod, Nat.cast_mul, one_div_mul_one_div]

variable {branch : Nat → Nat} {n m t : Nat}

def rawEquiv (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (child : Fin (branch n)) :
    ((Fin calls → Square slots child) × Arrays (childSlots slots child) rows) ≃
      ChildBlockCardinality.Raw calls rows (childSlots slots child) := Equiv.refl _

def arrayComponent (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    (child : Fin (branch n)) → FiniteDistribution (Arrays (childSlots slots child) rows) :=
  ChildBlockMixture.component
    (fun child => WholeArraySampler.law rows repeats q (childSlots slots child)) chosen

def specialLaw (calls : Nat) (rows repeats : Nat → Nat) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (child : Fin (branch n)) :
    FiniteDistribution (ChildBlockCardinality.Raw calls rows (childSlots slots child)) :=
  @FiniteDistribution.transport
    ((Fin calls → Square slots child) × Arrays (childSlots slots child) rows)
    (ChildBlockCardinality.Raw calls rows (childSlots slots child))
    (instFintypeProd _ _) (ChildBlockCardinality.rawFintype calls rows (childSlots slots child))
    ((FiniteProduct.law (fun _ : Fin calls => specialSquareLaw repeats q slots child)).product
      (WholeArraySampler.law rows repeats q (childSlots slots child)))
    (rawEquiv calls rows slots child)

def componentLaw (calls : Nat) (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (child : Fin (branch n)) :
    FiniteDistribution (ChildBlockCardinality.Raw calls rows (childSlots slots child)) :=
  @FiniteDistribution.transport
    ((Fin calls → Square slots child) × Arrays (childSlots slots child) rows)
    (ChildBlockCardinality.Raw calls rows (childSlots slots child))
    (instFintypeProd _ _) (ChildBlockCardinality.rawFintype calls rows (childSlots slots child))
    ((callComponent calls repeats chosen q slots child).product
      (arrayComponent rows repeats chosen q slots child)) (rawEquiv calls rows slots child)

theorem callComponent_uniform (calls : Nat) (repeats : Nat → Nat)
    (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (child : Fin (branch n)) (hne : child ≠ chosen) :
    callComponent calls repeats chosen q slots child =
      FiniteDistribution.uniform (Fin calls → Square slots child) := by
  have h := squareComponent_other repeats q slots chosen ⟨child, hne⟩
  unfold callComponent
  rw [h]
  exact UniformLinearImage.law_uniform

theorem componentLaw_eq (calls : Nat) (rows repeats : Nat → Nat)
    (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (child : Fin (branch n)) :
    componentLaw calls rows repeats chosen q slots child =
      ChildBlockMixture.component (specialLaw calls rows repeats q slots) chosen child := by
  by_cases h : child = chosen
  · subst child
    simp only [componentLaw, callComponent, squareComponent_self, arrayComponent,
      ChildBlockMixture.component, dite_eq_left rfl, dite_true, specialLaw]
  · have harray : arrayComponent rows repeats chosen q slots child =
        FiniteDistribution.uniform (Arrays (childSlots slots child) rows) :=
      dite_eq_right (Ne.symm h)
    rw [componentLaw, callComponent_uniform calls repeats chosen q slots child h, harray]
    rw [uniform_product]
    have huniform := @UniformConditioning.uniform_transport
      ((Fin calls → Square slots child) × Arrays (childSlots slots child) rows)
      (ChildBlockCardinality.Raw calls rows (childSlots slots child))
      (instFintypeProd _ _) (ChildBlockCardinality.rawFintype calls rows (childSlots slots child))
      inferInstance inferInstance (rawEquiv calls rows slots child)
    have hcomponent :
        ChildBlockMixture.component (specialLaw calls rows repeats q slots) chosen child =
          FiniteDistribution.uniform
            (ChildBlockCardinality.Raw calls rows (childSlots slots child)) := by
      simp only [ChildBlockMixture.component, dite_eq_right (Ne.symm h)]
    exact huniform.trans hcomponent.symm

abbrev SourceTape (calls : Nat) (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :=
  (Fin calls → ScalarTape repeats chosen q slots) ×
    WholeArraySampler.Tape rows repeats (.step chosen q) slots

def sourceLaw (calls : Nat) (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    FiniteDistribution (SourceTape calls rows repeats chosen q slots) :=
  (callsLaw calls repeats chosen q slots).product
    (WholeArraySampler.tapeLaw rows repeats (.step chosen q) slots)

def rawMap (calls : Nat) (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : SourceTape calls rows repeats chosen q slots) :
    (child : Fin (branch n)) → ChildBlockCardinality.Raw calls rows (childSlots slots child) :=
  fun child => rawEquiv calls rows slots child
    (callContributions calls repeats chosen q slots ω.1 child,
      OriginalBelowCut.below rows repeats chosen q slots ω.2 child)

@[simp] theorem rawMap_call (calls : Nat) (rows repeats : Nat → Nat)
    (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : SourceTape calls rows repeats chosen q slots) (child : Fin (branch n)) (call : Fin calls) :
    (rawMap calls rows repeats chosen q slots ω child).1 call =
      stepSquareMap repeats chosen q slots (ω.1 call) child := rfl

@[simp] theorem rawMap_array (calls : Nat) (rows repeats : Nat → Nat)
    (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : SourceTape calls rows repeats chosen q slots) (child : Fin (branch n))
    (node : Nodes branch n) :
    (rawMap calls rows repeats chosen q slots ω child).2 node =
      WholeArraySampler.evaluate rows repeats (.step chosen q) slots ω.2 (.inr (child, node)) := rfl

theorem rawMap_product_law (calls : Nat) (rows repeats : Nat → Nat)
    (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    (sourceLaw calls rows repeats chosen q slots).pushforward
        (rawMap calls rows repeats chosen q slots) =
      FiniteProduct.law (componentLaw calls rows repeats chosen q slots) := by
  calc
    _ = ((sourceLaw calls rows repeats chosen q slots).pushforward
        (fun ω => (callContributions calls repeats chosen q slots ω.1,
          OriginalBelowCut.below rows repeats chosen q slots ω.2))).pushforward
          (fun z child => rawEquiv calls rows slots child (z.1 child, z.2 child)) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = ((FiniteProduct.law (callComponent calls repeats chosen q slots)).product
        (FiniteProduct.law (arrayComponent rows repeats chosen q slots))).pushforward
          (fun z child => rawEquiv calls rows slots child (z.1 child, z.2 child)) := by
      rw [sourceLaw, FiniteDistribution.product_pushforward,
        callContributions_law, OriginalBelowCut.below_pushforward, arrayComponent]
    _ = _ := by
      have hpair := OriginalChildBlockProducts.pair_transport_law
        (Ω := fun child : Fin (branch n) => Fin calls → ↥(Square slots child))
        (Γ := fun child => Arrays (childSlots slots child) rows)
        (Δ := fun child => ChildBlockCardinality.Raw calls rows (childSlots slots child))
        (rawEquiv calls rows slots) (callComponent calls repeats chosen q slots)
        (arrayComponent rows repeats chosen q slots)
      apply FiniteDistribution.eq_of_weight_eq
      intro x
      have hw := congrFun (congrArg FiniteDistribution.weight hpair) x
      simpa only [componentLaw, FiniteProduct.law, FiniteDistribution.transport] using hw

theorem rawMap_law (calls : Nat) (rows repeats : Nat → Nat)
    (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    (sourceLaw calls rows repeats chosen q slots).pushforward
        (rawMap calls rows repeats chosen q slots) =
      ChildBlockMixture.special (specialLaw calls rows repeats q slots) chosen := by
  rw [rawMap_product_law]
  apply congrArg (fun laws : (child : Fin (branch n)) →
    FiniteDistribution (ChildBlockCardinality.Raw calls rows (childSlots slots child)) =>
      FiniteProduct.law laws)
  funext child
  exact componentLaw_eq calls rows repeats chosen q slots child

def observed (calls : Nat) (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : SourceTape calls rows repeats chosen q slots) :
    CutChildGrouping.Assembled (C := Fin calls) slots rows :=
  (fun call => RecursiveSampler.evaluate F2 repeats (.step chosen q) (LeafDomain slots) (ω.1 call),
    OriginalBelowCut.below rows repeats chosen q slots ω.2)

theorem assemble_rawMap (calls : Nat) (rows repeats : Nat → Nat)
    (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : SourceTape calls rows repeats chosen q slots) :
    CutChildGrouping.assemble slots rows (rawMap calls rows repeats chosen q slots ω) =
      observed calls rows repeats chosen q slots ω := by
  apply Prod.ext
  · funext call
    exact OriginalChildScalarAssembly.recursiveSum_callContributions
      calls repeats chosen q slots ω.1 call
  · rfl

theorem observed_law (calls : Nat) (rows repeats : Nat → Nat)
    (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    (sourceLaw calls rows repeats chosen q slots).pushforward
        (observed calls rows repeats chosen q slots) =
      (ChildBlockMixture.special (specialLaw calls rows repeats q slots) chosen).pushforward
        (CutChildGrouping.assemble slots rows) := by
  calc
    _ = ((sourceLaw calls rows repeats chosen q slots).pushforward
        (rawMap calls rows repeats chosen q slots)).pushforward
          (CutChildGrouping.assemble slots rows) := by
      rw [FiniteDistribution.pushforward_comp]
      congr 1
      funext ω
      exact (assemble_rawMap calls rows repeats chosen q slots ω).symm
    _ = _ := by rw [rawMap_law]

end
end PerfectCompleteness.OriginalChildBlocks

end

end OAI
