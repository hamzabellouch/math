import Mathlib

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

/-- A finite graph given by its edge list. Zero couplings can encode missing edges.
Edges are indexed separately so parallel edges are counted separately. -/
structure FiniteGraph (n m : ℕ) where
  left : Fin m → Fin n
  right : Fin m → Fin n
  coupling : Fin m → ℝ
  coupling_nonneg : ∀ e, 0 ≤ coupling e
  no_loops : ∀ e, left e ≠ right e

abbrev Spins (n : ℕ) := Fin n → Bool

def spin (b : Bool) : ℝ := if b then 1 else -1

noncomputable def energy {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (σ : Spins n) : ℝ :=
  (∑ e, G.coupling e * spin (σ (G.left e)) * spin (σ (G.right e))) +
    ∑ v, h v * spin (σ v)

noncomputable def weight {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (σ : Spins n) : ℝ := Real.exp (energy G h σ)

def AgreesOn {n : ℕ} (S : Finset (Fin n)) (σ τ : Spins n) : Prop :=
  ∀ v ∈ S, σ v = τ v

noncomputable def constrainedSum {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (P : Spins n → Prop) : ℝ := by
  classical
  exact ∑ σ, if P σ then weight G h σ else 0

/-- Conditional probability of σ_I=a, with σ_J=b and σ_F=τ prescribed.
All sums are finite and all fields are finite real numbers. -/
noncomputable def conditionalProb {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (a b τ : Spins n) : ℝ :=
  constrainedSum G h (fun σ => AgreesOn I σ a ∧ AgreesOn J σ b ∧ AgreesOn F σ τ) /
    constrainedSum G h (fun σ => AgreesOn J σ b ∧ AgreesOn F σ τ)

/-- Edges remaining after DELETION, not pinning, of F. -/
def keptEdges {n m : ℕ} (G : FiniteGraph n m) (F : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter (fun e => G.left e ∉ F ∧ G.right e ∉ F)

abbrev KeptVertex {n : ℕ} (F : Finset (Fin n)) := {v : Fin n // v ∉ F}

/-- Open-edge adjacency together with the two separate terminal identifications.
No virtual identification of common pins is present: those vertices are absent. -/
def comparisonRel {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) (u v : KeptVertex F) : Prop :=
  (u.val ∈ I ∧ v.val ∈ I) ∨ (u.val ∈ J ∧ v.val ∈ J) ∨
    ∃ e ∈ ω, (G.left e = u.val ∧ G.right e = v.val) ∨
      (G.left e = v.val ∧ G.right e = u.val)

/-- The equivalence closure implements components of the contracted open graph. -/
def comparisonSetoid {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) : Setoid (KeptVertex F) :=
  Relation.EqvGen.setoid (comparisonRel G I J F ω)

noncomputable def clusterCount {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) : ℕ :=
  Nat.card (Quotient (comparisonSetoid G I J F ω))

/-- Zero-field FK weight with q=2 and p_e=1-exp(-2 K_e).
Parallel edges may be retained: the measure after summing them is the measure
for the summed parallel coupling. Loops created by contraction do not change
components and cancel from connection probabilities. -/
noncomputable def fkWeight {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) : ℝ := by
  classical
  exact (2 : ℝ) ^ clusterCount G I J F ω *
    ∏ e ∈ keptEdges G F,
      if e ∈ ω then 1 - Real.exp (-2 * G.coupling e) else Real.exp (-2 * G.coupling e)

/-- Choose any i in I and j in J. The terminal connection is independent of
these choices because I and J are each identified. -/
noncomputable def qZero {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (i j : KeptVertex F) : ℝ := by
  classical
  exact (∑ ω ∈ (keptEdges G F).powerset,
    if (comparisonSetoid G I J F ω).r i j then fkWeight G I J F ω else 0) /
    ∑ ω ∈ (keptEdges G F).powerset, fkWeight G I J F ω

/-- Any probability mixture of source prescriptions. Full configurations
index the mixture, but only their restrictions to J are used. Thus this is
exactly the class of all mixtures on {-1,+1}^J. -/
noncomputable def mixtureProb {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (a τ : Spins n)
    (mix : Spins n → ℝ) : ℝ :=
  ∑ b, mix b * conditionalProb G h I J F a b τ

/-- Finite-graph comparison for arbitrary probability mixtures on both sides.
Dirac mixtures recover the conditional laws. -/
theorem finite_graph_comparison {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J)
    (a τ : Spins n) (mix mix' : Spins n → ℝ)
    (hmix : ∀ b, 0 ≤ mix b) (hmix' : ∀ b, 0 ≤ mix' b)
    (hmixsum : ∑ b, mix b = 1) (hmix'sum : ∑ b, mix' b = 1) :
    Real.exp (-4 * Real.artanh (qZero G I J F i j)) ≤
        mixtureProb G h I J F a τ mix / mixtureProb G h I J F a τ mix' ∧
      mixtureProb G h I J F a τ mix / mixtureProb G h I J F a τ mix' ≤
        Real.exp (4 * Real.artanh (qZero G I J F i j)) := by
  sorry

end BufferedIsing

end OAI
