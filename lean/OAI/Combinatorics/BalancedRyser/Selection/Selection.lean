import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Filter.AtTopBot.Basic
import OAI.Combinatorics.BalancedRyser.Incidence.FiniteAffinePlane

namespace OAI

open Filter
open scoped Topology

namespace Balanced
namespace Selection

noncomputable section
attribute [local instance] Classical.propDecidable

structure Input (I : Type*) (V : Type*) where
  graph : SimpleGraph V
  slot : V → I
  exceptional : V → Finset V

variable {I V : Type*} [Fintype I] [Fintype V]

def slotVertices (G : Input I V) (i : I) : Finset V :=
  Finset.univ.filter (fun v => G.slot v = i)

def neighbors (G : Input I V) (v : V) : Finset V :=
  Finset.univ.filter (G.graph.Adj v)

def GraphBounds (G : Input I V) (q : ℕ) (c C : ℝ) : Prop :=
  Fintype.card I = 2 * (q + 1) ∧
  (∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) ∧
  (∀ i, c * q ≤ ((slotVertices G i).card : ℝ) ∧ (slotVertices G i).card ≤ q) ∧
  (∀ v, ((neighbors G v).card : ℝ) ≤ C * q) ∧
  (∀ v i, (((neighbors G v) ∩ slotVertices G i).card : ℝ) ≤
    (q : ℝ) ^ (1 / 8 : ℝ)) ∧
  (∀ v, ((G.exceptional v).card : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ)) ∧
  (∀ v w, w ∉ G.exceptional v →
    (((neighbors G v) ∩ neighbors G w).card : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ)) ∧
  (∀ v w, w ∈ G.exceptional v → G.graph.Adj v w ∨ G.slot v = G.slot w)

def IsIndependentTransversal (G : Input I V) (a : I → V) : Prop :=
  (∀ i, G.slot (a i) = i) ∧ ∀ i j, i ≠ j → ¬ G.graph.Adj (a i) (a j)

structure OutputLaw (G : Input I V) where
  weight : (I → V) → ℝ
  nonnegative : ∀ a, 0 ≤ weight a
  mass_le_one : (∑ a, weight a) ≤ 1
  supported : ∀ a, 0 < weight a → IsIndependentTransversal G a

def successMass {G : Input I V} (law : OutputLaw G) : ℝ := ∑ a, law.weight a

def outcomeWeight {G : Input I V} (law : OutputLaw G) : Option (I → V) → ℝ
  | none => 1 - successMass law
  | some a => law.weight a

def cylinderMass {G : Input I V} (law : OutputLaw G) (J : Finset I)
    (prescribed : I → V) : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a : I → V => ∀ i ∈ J, a i = prescribed i), law.weight a

variable {q : ℕ} {P D L : Type*} [Fintype P] [Fintype D] [Fintype L]

def LineAssignment (G : Input I V) (A : FiniteAffine.Plane q P D L)
    (index : I ≃ (D × Bool)) (line : V → L) : Prop :=
  (∀ v, A.direction (line v) = (index (G.slot v)).1) ∧
  (∀ v w, G.slot v = G.slot w → line v = line w → v = w)

def TrackedSets (A : FiniteAffine.Plane q P D L) (T : L → Finset P) (c₀ : ℝ) : Prop :=
  ∀ ℓ, T ℓ ⊆ A.linePoints ℓ ∧ c₀ * q ≤ ((T ℓ).card : ℝ)

def finalTracked (A : FiniteAffine.Plane q P D L) (line : V → L)
    (T : L → Finset P) (a : I → V) (ℓ : L) : Finset P :=
  (T ℓ).filter (fun p => ∀ i, line (a i) ≠ ℓ → ¬ A.incident p (line (a i)))

def occupancyFailureMass {G : Input I V} (law : OutputLaw G)
    (A : FiniteAffine.Plane q P D L) (line : V → L) (T : L → Finset P) (ρ : ℝ) : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a : I → V =>
    ∃ ℓ : L, ((finalTracked A line T a ℓ).card : ℝ) < ρ * q), law.weight a

end
end Selection

def SelectionStatement.{u, v, w} : Prop :=
  ∀ c C c₀ : ℝ, 0 < c → 0 < C → 0 < c₀ → c₀ ≤ 1 →
    ∃ K ρ : ℝ, ∃ ε : ℕ → ℝ, ∃ q₀ : ℕ,
      0 < K ∧ 0 < ρ ∧ (∀ q, 0 ≤ ε q) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ q : ℕ, q₀ ≤ q →
      ∀ (I : Type u) (V : Type v) [Fintype I] [Fintype V],
      ∀ G : Selection.Input I V, Selection.GraphBounds G q c C →
      ∃ law : Selection.OutputLaw G,
        1 - ε q ≤ Selection.successMass law ∧
        (∀ (J : Finset I) (prescribed : I → V),
          Selection.cylinderMass law J prescribed ≤ (K / (q : ℝ)) ^ J.card) ∧
        (∀ (P D L : Type w) [Fintype P] [Fintype D] [Fintype L],
          ∀ (A : FiniteAffine.Plane q P D L) (index : I ≃ (D × Bool)) (line : V → L),
          Selection.LineAssignment G A index line →
          ∀ T : L → Finset P, Selection.TrackedSets A T c₀ →
            Selection.occupancyFailureMass law A line T ρ ≤ ε q)

end Balanced

end OAI
