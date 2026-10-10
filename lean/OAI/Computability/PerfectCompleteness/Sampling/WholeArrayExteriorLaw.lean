import OAI.Computability.PerfectCompleteness.Machines.OwnInputReferenceLemmas
import OAI.Computability.PerfectCompleteness.Sampling.WholeArrayHiddenLaw

namespace OAI

section

namespace PerfectCompleteness.WholeArrayExteriorLaw

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces HierarchicalArrays DescendantSpaces WholeArraySampler
open WholeArrayHiddenLaw

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

instance exteriorFintype (rows : Nat → Nat)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (lower : Nodes branch (n + 1)) :
    Fintype (OwnInputReference.Exterior slots rows (Sum.inl ()) lower) :=
  OwnInputReference.exteriorFintype (branch := branch) (n := n + 1) (t := t)
    slots rows (Sum.inl ()) lower

abbrev NonRoot (branch : Nat → Nat) (n : Nat) :=
  {node : Nodes branch (n + 1) // node ≠ Sum.inl ()}

def children (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (rest : RestTape rows repeats i p slots) :
    (j : Fin (branch n)) → Arrays (childSlots slots j) rows :=
  WholeArraySampler.childrenAt slots rows i
    (WholeArraySampler.evaluate rows repeats p (childSlots slots i)
      (rest ⟨Sum.inr (Sum.inl ()), by simp⟩))
    (fun j => rest ⟨Sum.inr (Sum.inr j), by simp⟩)

def nodeArray (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (rest : RestTape rows repeats i p slots) (node : NonRoot branch n) :
    Fin (rows (Nodes.height node.val)) → H (nodeSlots slots node.val) :=
  match node with
  | ⟨.inl u, h⟩ => False.elim (h (by cases u; rfl))
  | ⟨.inr (j, child), _⟩ => children rows repeats i p slots rest j child

theorem nodeArray_evaluate (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape rows repeats (.step i p) slots) (node : NonRoot branch n) :
    nodeArray rows repeats i p slots (splitRoot rows repeats i p slots ω).2 node =
      WholeArraySampler.evaluate rows repeats (.step i p) slots ω node.val := by
  rcases node with ⟨node, hnode⟩
  cases node with
  | inl u =>
      cases u
      exact False.elim (hnode rfl)
  | inr pair =>
      rcases pair with ⟨j, child⟩
      rfl

def exterior (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (lower : Nodes branch (n + 1)) (hne : lower ≠ Sum.inl ())
    (rest : RestTape rows repeats i p slots) :
    OwnInputReference.Exterior slots rows (Sum.inl ()) lower where
  otherArrays node := nodeArray rows repeats i p slots rest ⟨node.val, node.property.1⟩
  lowerRows := nodeArray rows repeats i p slots rest ⟨lower, hne⟩

def readExterior (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (lower : Nodes branch (n + 1))
    (ω : Tape rows repeats (.step i p) slots) :
    OwnInputReference.Exterior slots rows (Sum.inl ()) lower where
  otherArrays node := WholeArraySampler.evaluate rows repeats (.step i p) slots ω node.val
  lowerRows := WholeArraySampler.evaluate rows repeats (.step i p) slots ω lower

theorem exterior_read_splitRoot (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (lower : Nodes branch (n + 1)) (hne : lower ≠ Sum.inl ())
    (ω : Tape rows repeats (.step i p) slots) :
    exterior rows repeats i p slots lower hne (splitRoot rows repeats i p slots ω).2 =
      readExterior rows repeats i p slots lower ω := by
  unfold exterior readExterior
  congr 1
  · funext node
    exact nodeArray_evaluate rows repeats i p slots ω ⟨node.val, node.property.1⟩
  · exact nodeArray_evaluate rows repeats i p slots ω ⟨lower, hne⟩

def exteriorLaw (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (lower : Nodes branch (n + 1)) (hne : lower ≠ Sum.inl ()) :
    FiniteDistribution (OwnInputReference.Exterior slots rows (Sum.inl ()) lower) :=
  (restLaw rows repeats i p slots).pushforward (exterior rows repeats i p slots lower hne)

theorem split_exterior_law (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (lower : Nodes branch (n + 1)) (hne : lower ≠ Sum.inl ())
    (W : Submodule F2 (Fin (rows (n + 1)) → F2)) :
    (WholeArraySampler.tapeLaw rows repeats (.step i p) slots).pushforward
        (fun ω => ((split rows repeats i p slots W ω).1,
          ((split rows repeats i p slots W ω).2.1,
            readExterior rows repeats i p slots lower ω))) =
      HiddenBucketBias.exposedLaw W (scalarLaw repeats i p slots)
        (exteriorLaw rows repeats i p slots lower hne) := by
  have hread (ω : Tape rows repeats (.step i p) slots) :
      exterior rows repeats i p slots lower hne (split rows repeats i p slots W ω).2.2 =
        readExterior rows repeats i p slots lower ω :=
    exterior_read_splitRoot rows repeats i p slots lower hne ω
  simpa only [hread, exteriorLaw] using
    split_readout_law rows repeats i p slots W (exterior rows repeats i p slots lower hne)

end
end PerfectCompleteness.WholeArrayExteriorLaw

end

end OAI
