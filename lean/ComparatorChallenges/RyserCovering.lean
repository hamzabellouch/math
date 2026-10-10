import Mathlib

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample

abbrev Hypergraph (V : Type*) := Finset (Finset V)

section

variable {V : Type*} [DecidableEq V]

def IsCover (H : Hypergraph V) (C : Finset V) : Prop :=
  ∀ e ∈ H, ∃ v ∈ C, v ∈ e

def Intersecting (H : Hypergraph V) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).Nonempty

attribute [-instance] instDecidablePairwiseCoeFinsetOfDecidableEqOfDecidableRel in
def matchings (H : Hypergraph V) : Finset (Hypergraph V) := by
  classical
  exact H.powerset.filter fun M => (M : Set (Finset V)).Pairwise Disjoint

def matchingNumber (H : Hypergraph V) : ℕ := (matchings H).sup Finset.card

def coverCardinalities (H : Hypergraph V) : Set ℕ :=
  {n | ∃ C : Finset V, IsCover H C ∧ C.card = n}

def coverNumber (H : Hypergraph V) : ℕ := sInf (coverCardinalities H)

def PartiteUniform {I : Type*} (part : V → I) (H : Hypergraph V) : Prop :=
  ∀ e ∈ H, ∀ i : I, ∃! v : V, v ∈ e ∧ part v = i

def RPartiteUniform (r : ℕ) (H : Hypergraph V) : Prop :=
  ∃ part : V → Fin r, PartiteUniform part H

end

def CounterexampleRank (r : ℕ) : Prop :=
  ∃ (V : Type) (fin : Fintype V) (dec : DecidableEq V),
    letI : Fintype V := fin
    letI : DecidableEq V := dec
    ∃ H : Hypergraph V,
      0 < r ∧ H.Nonempty ∧ RPartiteUniform r H ∧ Intersecting H ∧
        (∃ C : Finset V, IsCover H C) ∧ matchingNumber H = 1 ∧ coverNumber H = r

theorem exists_prime_eventually_counterexampleRank :
    ∃ p : ℕ, p.Prime ∧ 5 < p ∧ p % 3 = 2 ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n.Prime → 2 < n →
        CounterexampleRank (p ^ n + 1) := by
  sorry

end RyserCoveringCounterexample

end

end OAI
