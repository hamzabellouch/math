import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Lattice.Nat

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample

abbrev Hypergraph (V : Type*) := Finset (Finset V)

variable {V : Type*} [DecidableEq V]

def IsCover (H : Hypergraph V) (C : Finset V) : Prop :=
  ∀ e ∈ H, ∃ v ∈ C, v ∈ e

def NonemptyEdges (H : Hypergraph V) : Prop := ∀ e ∈ H, e.Nonempty

def Intersecting (H : Hypergraph V) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).Nonempty

def IsMatching (H M : Hypergraph V) : Prop :=
  M ⊆ H ∧ (M : Set (Finset V)).Pairwise Disjoint

def matchings (H : Hypergraph V) : Finset (Hypergraph V) := by
  classical
  exact H.powerset.filter fun M => (M : Set (Finset V)).Pairwise Disjoint

def matchingNumber (H : Hypergraph V) : ℕ := (matchings H).sup Finset.card

def coverCardinalities (H : Hypergraph V) : Set ℕ :=
  {n | ∃ C : Finset V, IsCover H C ∧ C.card = n}

def coverNumber (H : Hypergraph V) : ℕ := sInf (coverCardinalities H)

def Uniform (r : ℕ) (H : Hypergraph V) : Prop := ∀ e ∈ H, e.card = r

def PartiteUniform {I : Type*} (part : V → I) (H : Hypergraph V) : Prop :=
  ∀ e ∈ H, ∀ i : I, ∃! v : V, v ∈ e ∧ part v = i

def RPartiteUniform (r : ℕ) (H : Hypergraph V) : Prop :=
  ∃ part : V → Fin r, PartiteUniform part H

end RyserCoveringCounterexample

end

end OAI
