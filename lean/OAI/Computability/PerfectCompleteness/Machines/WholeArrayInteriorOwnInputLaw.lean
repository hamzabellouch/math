import OAI.Computability.PerfectCompleteness.Foundations.WholeArrayPositiveSplit
import OAI.Computability.PerfectCompleteness.Machines.WholeArrayOwnInputLaw

namespace OAI

section

namespace PerfectCompleteness.WholeArrayInteriorOwnInputLaw

open scoped BigOperators TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

abbrev F2 := ZMod 2

noncomputable section

private theorem pushforward_eq_of_readout_weights {A B : Type*} [iA : Fintype A]
    {i j : Fintype B} (μ : FiniteDistribution A) (f g : A → B)
    (ν : @FiniteDistribution B i) (ν' : @FiniteDistribution B j)
    (h : @FiniteDistribution.pushforward A B iA i μ f = ν)
    (hread : ∀ a, f a = g a)
    (hweight : ∀ b, @FiniteDistribution.weight B i ν b = @FiniteDistribution.weight B j ν' b) :
    @FiniteDistribution.pushforward A B iA j μ g = ν' := by
  have hfg : f = g := funext hread
  cases hfg
  apply @FiniteDistribution.eq_of_weight_eq B j
  intro b
  calc
    @FiniteDistribution.weight B j (@FiniteDistribution.pushforward A B iA j μ f) b =
        @FiniteDistribution.weight B i (@FiniteDistribution.pushforward A B iA i μ f) b := rfl
    _ = @FiniteDistribution.weight B i ν b :=
      congrFun (congrArg (@FiniteDistribution.weight B i) h) b
    _ = @FiniteDistribution.weight B j ν' b := hweight b

variable {branch : Nat → Nat} {N t : Nat}

abbrev fullPath (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower) :=
  (Nodes.path upper).append cut.path

abbrev RawExterior (rows repeats : Nat → Nat)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower) :=
  WholeArrayPositiveSplit.Exterior rows repeats (Nodes.path upper) cut.path slots

def exterior (rows repeats : Nat → Nat)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower)
    (raw : RawExterior rows repeats slots upper lower cut) :
    OwnInputReference.Exterior slots rows upper lower where
  otherArrays node := WholeArrayPositiveSplit.nodeArray rows repeats
    (Nodes.path upper) cut.path cut.proper slots raw node.val (by
      simpa only [WholeArrayInteriorExterior.selectedNode_nodePath] using node.property.1)
  lowerRows := WholeArrayPositiveSplit.nodeArray rows repeats
    (Nodes.path upper) cut.path cut.proper slots raw lower (by
      simpa only [WholeArrayInteriorExterior.selectedNode_nodePath] using cut.upper_ne_lower.symm)

def readExterior (rows repeats : Nat → Nat)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower)
    (ω : WholeArraySampler.Tape rows repeats (fullPath upper lower cut) slots) :
    OwnInputReference.Exterior slots rows upper lower where
  otherArrays node := WholeArraySampler.evaluate rows repeats (fullPath upper lower cut) slots ω node.val
  lowerRows := WholeArraySampler.evaluate rows repeats (fullPath upper lower cut) slots ω lower

theorem exterior_split (rows repeats : Nat → Nat)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower)
    (W : Submodule F2 (Block rows upper))
    (ω : WholeArraySampler.Tape rows repeats (fullPath upper lower cut) slots) :
    exterior rows repeats slots upper lower cut
        (WholeArrayPositiveSplit.split rows repeats (Nodes.path upper) cut.path
          cut.proper slots W ω).2.2 =
      readExterior rows repeats slots upper lower cut ω := by
  unfold exterior readExterior
  congr 1
  · funext node
    exact WholeArrayPositiveSplit.nodeArray_split rows repeats
      (Nodes.path upper) cut.path cut.proper slots W ω node.val (by
        simpa only [WholeArrayInteriorExterior.selectedNode_nodePath] using node.property.1)
  · exact WholeArrayPositiveSplit.nodeArray_split rows repeats
      (Nodes.path upper) cut.path cut.proper slots W ω lower (by
        simpa only [WholeArrayInteriorExterior.selectedNode_nodePath] using cut.upper_ne_lower.symm)

def exteriorLaw (rows repeats : Nat → Nat)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower) :
    FiniteDistribution (OwnInputReference.Exterior slots rows upper lower) :=
  (WholeArrayPositiveSplit.exteriorLaw rows repeats (Nodes.path upper) cut.path slots).pushforward
    (exterior rows repeats slots upper lower cut)

def exposedRead (rows repeats : Nat → Nat)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower)
    (W : Submodule F2 (Block rows upper))
    (ω : WholeArraySampler.Tape rows repeats (fullPath upper lower cut) slots) :
    OwnInputReference.RawSample slots rows upper lower W repeats cut :=
  let parts := WholeArrayPositiveSplit.split rows repeats (Nodes.path upper) cut.path cut.proper slots W ω
  (parts.1, (parts.2.1, readExterior rows repeats slots upper lower cut ω))

theorem exposedRead_law (rows repeats : Nat → Nat)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower)
    (W : Submodule F2 (Block rows upper)) :
    (WholeArraySampler.tapeLaw rows repeats (fullPath upper lower cut) slots).pushforward
        (exposedRead rows repeats slots upper lower cut W) =
      OwnInputReference.rawLaw slots rows upper lower W repeats cut
        (exteriorLaw rows repeats slots upper lower cut) := by
  have hsplit := WholeArrayPositiveSplit.split_readout_law rows repeats
    (Nodes.path upper) cut.path cut.proper slots W
    (exterior rows repeats slots upper lower cut)
  refine pushforward_eq_of_readout_weights _ _ _ _ _ hsplit ?_ ?_
  · intro ω
    exact congrArg
      (fun external =>
        ((WholeArrayPositiveSplit.split rows repeats (Nodes.path upper) cut.path
          cut.proper slots W ω).1,
          ((WholeArrayPositiveSplit.split rows repeats (Nodes.path upper) cut.path
            cut.proper slots W ω).2.1, external)))
      (exterior_split rows repeats slots upper lower cut W ω)
  · intro x
    rfl

def readInput (rows repeats : Nat → Nat)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower)
    (W : Submodule F2 (Block rows upper)) (a : Block rows lower)
    (data : HiddenBucketBias.VisibleTape W
        (OwnInputReference.ScalarSample slots upper lower repeats cut) ×
      RawExterior rows repeats slots upper lower cut) :
    OwnInputReference.Input slots rows upper lower W a :=
  OwnInputReference.readInput slots rows upper lower W a
    (RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper)))
    (data.1, exterior rows repeats slots upper lower cut data.2)

def ownInput (rows repeats : Nat → Nat)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower)
    (W : Submodule F2 (Block rows upper)) (a : Block rows lower)
    (ω : WholeArraySampler.Tape rows repeats (fullPath upper lower cut) slots) :
    OwnInputReference.Input slots rows upper lower W a :=
  OwnInputReference.readInput slots rows upper lower W a
    (RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper)))
    (exposedRead rows repeats slots upper lower cut W ω).2

theorem readInput_split (rows repeats : Nat → Nat)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower)
    (W : Submodule F2 (Block rows upper)) (a : Block rows lower)
    (ω : WholeArraySampler.Tape rows repeats (fullPath upper lower cut) slots) :
    readInput rows repeats slots upper lower cut W a
        (WholeArrayPositiveSplit.split rows repeats (Nodes.path upper) cut.path cut.proper slots W ω).2 =
      ownInput rows repeats slots upper lower cut W a ω := by
  unfold readInput ownInput exposedRead
  rw [exterior_split]

def hiddenOutput (rows repeats : Nat → Nat)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower)
    (W : Submodule F2 (Block rows upper))
    (ω : WholeArraySampler.Tape rows repeats (fullPath upper lower cut) slots) :
    W ⊗[F2] OwnInputReference.UpperSpace slots upper :=
  HiddenBucketBias.hiddenSum W
    (RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper)))
    (exposedRead rows repeats slots upper lower cut W ω).1

theorem conditional_referenceLaw (rows repeats : Nat → Nat)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower)
    (W : Submodule F2 (Block rows upper)) (a : Block rows lower)
    (observed : OwnInputReference.Input slots rows upper lower W a)
    (positive : 0 <
      (WholeArraySampler.tapeLaw rows repeats (fullPath upper lower cut) slots).probability
        (fun ω => decide (ownInput rows repeats slots upper lower cut W a ω = observed))) :
    ((WholeArraySampler.tapeLaw rows repeats (fullPath upper lower cut) slots).condition
      (fun ω => decide (ownInput rows repeats slots upper lower cut W a ω = observed)) positive).pushforward
        (hiddenOutput rows repeats slots upper lower cut W) =
      OwnInputReference.referenceLaw slots rows upper lower W repeats cut := by
  let μ := WholeArraySampler.tapeLaw rows repeats (fullPath upper lower cut) slots
  let read := exposedRead rows repeats slots upper lower cut W
  let ν := OwnInputReference.rawLaw slots rows upper lower W repeats cut
    (exteriorLaw rows repeats slots upper lower cut)
  let event := OwnInputReference.inputEvent slots rows upper lower W a repeats cut observed
  let eval := RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper))
  have hread : μ.pushforward read = ν := exposedRead_law rows repeats slots upper lower cut W
  have positive' : 0 < ν.probability event := by
    rw [← hread, FiniteDistribution.probability_pushforward]
    exact positive
  have hcondition :
      (μ.condition (fun ω => event (read ω)) positive).pushforward read =
        ν.condition event positive' := by
    simpa only [hread] using
      WholeArrayOwnInputLaw.condition_pushforward μ read event positive
  calc
    _ = ((μ.condition (fun ω => event (read ω)) positive).pushforward read).pushforward
        (fun z => HiddenBucketBias.hiddenSum W eval z.1) :=
      (FiniteDistribution.pushforward_comp _ read
        (fun z => HiddenBucketBias.hiddenSum W eval z.1)).symm
    _ = _ := by
      rw [hcondition]
      exact OwnInputReference.conditional_referenceLaw slots rows upper lower W a repeats cut
        (exteriorLaw rows repeats slots upper lower cut) observed positive'

end
end PerfectCompleteness.WholeArrayInteriorOwnInputLaw

end

end OAI
