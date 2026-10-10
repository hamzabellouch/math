import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalBatchFacts
import OAI.Combinatorics.KMedian.Rounding.RationalBatchEnumeration

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch
variable {I : Type} [LinearOrder I] [Fintype I]

abbrev Event (I : Type) [DecidableEq I] [Fintype I] (g β : ℚ) :=
  (G : I → Finset I) × Finset (HeavyAction (graph G) (heavySet (graphMass G g) β))

def events (μ : SparseIntegerLaw (I → Finset I)) (Δ : ℕ) (g β p φ : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1) : SparseIntegerLaw (Event I g β) :=
  μ.bindIndexed (fun i =>
    let G := μ.states[i.val]
    (proposal G Δ g β p φ hp hφ hupper
      (enumeration (graph G) (heavySet (graphMass G g) β))).map (fun Z => ⟨G,Z⟩))

theorem events_length (μ : SparseIntegerLaw (I → Finset I)) (Δ : ℕ) (g β p φ : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1) :
    (events μ Δ g β p φ hp hφ hupper).length ≤
      μ.length*(2*((Fintype.card I+(Fintype.card I)^2+1)^4+1)) := by
  apply SparseIntegerLaw.bindIndexed_length
  intro i
  change (proposal _ Δ g β p φ hp hφ hupper _).length ≤ _
  unfold proposal
  apply (SparseEnumeratedBatch.length _ _ _ _ _ _ _).trans
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_right
  apply Nat.pow_le_pow_left
  exact Nat.add_le_add_right (action_card _ _) 1

theorem events_expectation (μ : SparseIntegerLaw (I → Finset I)) (Δ : ℕ) (g β p φ : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1) (V : Event I g β → ℝ) :
    (events μ Δ g β p φ hp hφ hupper).expectation V=
      μ.expectation (fun G =>
        (proposal G Δ g β p φ hp hφ hupper
          (enumeration (graph G) (heavySet (graphMass G g) β))).expectation (fun Z => V ⟨G,Z⟩)) := by
  rw [events,SparseIntegerLaw.expectation_bindIndexed]
  simp only [SparseIntegerLaw.expectation_def,SparseIntegerLaw.map,Vector.getElem_map]

theorem events_property (μ : SparseIntegerLaw (I → Finset I)) (Δ : ℕ) (g β p φ : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (Q : Event I g β → Prop)
    (hQ : ∀ i : Fin μ.length, ∀ Z : Finset (HeavyAction (graph μ.states[i.val])
      (heavySet (graphMass μ.states[i.val] g) β)), Q ⟨μ.states[i.val],Z⟩) :
    ∀ i : Fin (events μ Δ g β p φ hp hφ hupper).length,
      Q (events μ Δ g β p φ hp hφ hupper).states[i.val] := by
  apply SparseIntegerLaw.bindIndexed_property _ _ Q
  intro i j
  have he := SparseIntegerLaw.map_states
    (proposal μ.states[i.val] Δ g β p φ hp hφ hupper
      (enumeration (graph μ.states[i.val]) (heavySet (graphMass μ.states[i.val] g) β)))
    (fun Z => (⟨μ.states[i.val],Z⟩ : Event I g β)) j
  rw [he]
  exact hQ i _

end MetricKMedian.RationalBatchData
end
end

end OAI
