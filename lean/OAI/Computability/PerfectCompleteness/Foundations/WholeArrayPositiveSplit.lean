import OAI.Computability.PerfectCompleteness.Foundations.WholeArrayInteriorExteriorLemmas
import OAI.Computability.PerfectCompleteness.Sampling.WholeArrayInteriorHiddenLaw

namespace OAI

section

namespace PerfectCompleteness.WholeArrayPositiveSplit

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays WholeArraySampler
open WholeArraySubtreeSplit
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {N h k t : Nat}

abbrev ScalarTape (repeats : Nat → Nat) (p : Path branch N h) (q : Path branch h k)
    (slots : Slots branch N → Fin t → MixedSupport.Slot) :=
  RecursiveSampler.Tape F2 repeats q (LeafDomain (subtreeSlots p slots))

instance scalarTapeFintype (repeats : Nat → Nat) (p : Path branch N h)
    (q : Path branch h k) (slots : Slots branch N → Fin t → MixedSupport.Slot) :
    Fintype (ScalarTape repeats p q slots) := by
  letI : (j : RecursiveSampler.DrawIndex repeats q) →
      Fintype (RecursiveSampler.DrawSpace F2 repeats q
        (LeafDomain (subtreeSlots p slots)) j) :=
    fun j => RecursiveSampler.drawSpaceFintype F2 repeats q
      (LeafDomain (subtreeSlots p slots)) j
  change Fintype ((j : RecursiveSampler.DrawIndex repeats q) →
    RecursiveSampler.DrawSpace F2 repeats q (LeafDomain (subtreeSlots p slots)) j)
  infer_instance

def RestTape (rows repeats : Nat → Nat) :
    {h k : Nat} → (q : Path branch h k) →
      (Slots branch h → Fin t → MixedSupport.Slot) → Type
  | _, _, .refl _, _ => Unit
  | _, _, .step i q, slots => WholeArrayHiddenLaw.RestTape rows repeats i q slots

@[instance_reducible] def restTapeFintypeAux (rows repeats : Nat → Nat) :
    {h k : Nat} → (q : Path branch h k) →
      (slots : Slots branch h → Fin t → MixedSupport.Slot) →
        Fintype (RestTape rows repeats q slots)
  | _, _, .refl _, _ => inferInstanceAs (Fintype Unit)
  | _, _, .step i q, slots => WholeArrayHiddenLaw.restTapeFintype rows repeats i q slots

instance restTapeFintype (rows repeats : Nat → Nat) (q : Path branch h k)
    (slots : Slots branch h → Fin t → MixedSupport.Slot) :
    Fintype (RestTape rows repeats q slots) :=
  restTapeFintypeAux rows repeats q slots

abbrev Exterior (rows repeats : Nat → Nat) (p : Path branch N h) (q : Path branch h k)
    (slots : Slots branch N → Fin t → MixedSupport.Slot) :=
  Complement rows repeats p q slots × RestTape rows repeats q (subtreeSlots p slots)

def scalarLaw (repeats : Nat → Nat) (p : Path branch N h) (q : Path branch h k)
    (slots : Slots branch N → Fin t → MixedSupport.Slot) :
    FiniteDistribution (ScalarTape repeats p q slots) :=
  RecursiveSampler.tapeLaw F2 repeats q (LeafDomain (subtreeSlots p slots))

def restLaw (rows repeats : Nat → Nat) :
    {h k : Nat} → (q : Path branch h k) →
      (slots : Slots branch h → Fin t → MixedSupport.Slot) →
        FiniteDistribution (RestTape rows repeats q slots)
  | _, _, .refl _, _ => FiniteDistribution.uniform Unit
  | _, _, .step i q, slots => WholeArrayHiddenLaw.restLaw rows repeats i q slots

def exteriorLaw (rows repeats : Nat → Nat) (p : Path branch N h) (q : Path branch h k)
    (slots : Slots branch N → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Exterior rows repeats p q slots) :=
  (complementLaw rows repeats p q slots).product
    (restLaw rows repeats q (subtreeSlots p slots))

def split (rows repeats : Nat → Nat) (p : Path branch N h) (q : Path branch h k)
    (hproper : k < h) (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows h) → F2))
    (ω : Tape rows repeats (p.append q) slots) :
    HiddenBucketBias.HiddenTape W (ScalarTape repeats p q slots) ×
      (HiddenBucketBias.VisibleTape W (ScalarTape repeats p q slots) ×
        Exterior rows repeats p q slots) := by
  cases q with
  | refl => exact False.elim ((Nat.lt_irrefl _) hproper)
  | step i q => exact WholeArrayInteriorHiddenLaw.split rows repeats p i q slots W ω

theorem split_law (rows repeats : Nat → Nat) (p : Path branch N h) (q : Path branch h k)
    (hproper : k < h) (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows h) → F2)) :
    (WholeArraySampler.tapeLaw rows repeats (p.append q) slots).pushforward
        (split rows repeats p q hproper slots W) =
      (HiddenBucketBias.hiddenTapeLaw W (scalarLaw repeats p q slots)).product
        ((HiddenBucketBias.visibleTapeLaw W (scalarLaw repeats p q slots)).product
          (exteriorLaw rows repeats p q slots)) := by
  cases q with
  | refl => exact False.elim ((Nat.lt_irrefl _) hproper)
  | step i q => exact WholeArrayInteriorHiddenLaw.split_law rows repeats p i q slots W

theorem split_readout_law {E : Type*} [Fintype E]
    (rows repeats : Nat → Nat) (p : Path branch N h) (q : Path branch h k)
    (hproper : k < h) (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows h) → F2))
    (read : Exterior rows repeats p q slots → E) :
    (WholeArraySampler.tapeLaw rows repeats (p.append q) slots).pushforward
        (fun ω => ((split rows repeats p q hproper slots W ω).1,
          ((split rows repeats p q hproper slots W ω).2.1,
            read (split rows repeats p q hproper slots W ω).2.2))) =
      HiddenBucketBias.exposedLaw W (scalarLaw repeats p q slots)
        ((exteriorLaw rows repeats p q slots).pushforward read) := by
  cases q with
  | refl => exact False.elim ((Nat.lt_irrefl _) hproper)
  | step i q =>
      exact WholeArrayInteriorHiddenLaw.split_readout_law rows repeats p i q slots W read

def nodeArray (rows repeats : Nat → Nat) (p : Path branch N h) (q : Path branch h k)
    (hproper : k < h) (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (external : Exterior rows repeats p q slots) (node : Nodes branch N)
    (hnode : node ≠ WholeArrayInteriorExterior.selectedNode p
      (Nat.zero_lt_of_lt hproper)) :
    Fin (rows (Nodes.height node)) → H (nodeSlots slots node) := by
  cases q with
  | refl => exact False.elim ((Nat.lt_irrefl _) hproper)
  | step i q =>
      exact WholeArrayInteriorExterior.nodeArray rows repeats p i q slots external ⟨node, hnode⟩

theorem nodeArray_split (rows repeats : Nat → Nat) (p : Path branch N h)
    (q : Path branch h k) (hproper : k < h)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows h) → F2))
    (ω : Tape rows repeats (p.append q) slots) (node : Nodes branch N)
    (hnode : node ≠ WholeArrayInteriorExterior.selectedNode p
      (Nat.zero_lt_of_lt hproper)) :
    nodeArray rows repeats p q hproper slots
        (split rows repeats p q hproper slots W ω).2.2 node hnode =
      WholeArraySampler.evaluate rows repeats (p.append q) slots ω node := by
  cases q with
  | refl => exact False.elim ((Nat.lt_irrefl _) hproper)
  | step i q =>
      exact WholeArrayInteriorExterior.nodeArray_split rows repeats p i q slots W ω
        ⟨node, hnode⟩

end
end PerfectCompleteness.WholeArrayPositiveSplit

end

end OAI
