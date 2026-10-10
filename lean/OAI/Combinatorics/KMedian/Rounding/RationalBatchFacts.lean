import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseEnumeratedBatch
import OAI.Combinatorics.KMedian.Rounding.RationalBatchData

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch PhysicalPotential
variable {I E : Type} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

omit [Fintype I] in
theorem conflicts_eq (D : Actions I E) (Δ : ℕ) (e : E) :
    conflicts D Δ e=balancedConflicts D Δ e := by
  unfold conflicts balancedConflicts balanced balancedActions
  split_ifs with he
  · ext f
    constructor
    · intro hf
      obtain ⟨hb,hne,i,hi⟩ := mem_filter.mp hf
      apply mem_erase.mpr
      refine ⟨hne,mem_inter.mpr ⟨?_,hb⟩⟩
      exact (FiniteGraph.mem_touching _ _ _).mpr ⟨i,(mem_inter.mp hi).1,(mem_inter.mp hi).2⟩
    · intro hf
      obtain ⟨hne,hf⟩ := mem_erase.mp hf
      obtain ⟨ht,hb⟩ := mem_inter.mp hf
      obtain ⟨i,hi,hif⟩ := (FiniteGraph.mem_touching _ _ _).mp ht
      exact mem_filter.mpr ⟨hb,hne,⟨i,mem_inter.mpr ⟨hi,hif⟩⟩⟩
  · rfl

omit [DecidableEq I] [Fintype I] in
theorem bias_bounds (m : I → ℚ) {p φ : ℚ} (hp : 0 ≤ p) (hφ : 0 ≤ φ) (i : I) :
    p ≤ bias m p φ i ∧ bias m p φ i ≤ (1+φ)*p := by
  unfold bias
  split_ifs <;> constructor <;> nlinarith only [mul_nonneg hp hφ]

omit [DecidableEq I] [Fintype I] in
theorem bias_probability (m : I → ℚ) {p φ : ℚ} (hp : 0 ≤ p) (hφ : 0 ≤ φ)
    (hupper : (1+φ)*p ≤ 1) (i : I) : 0 ≤ bias m p φ i ∧ bias m p φ i ≤ 1 :=
  ⟨hp.trans (bias_bounds m hp hφ i).1,(bias_bounds m hp hφ i).2.trans hupper⟩

def proposal (G : I → Finset I) (Δ : ℕ) (g b p φ : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1) {n : ℕ}
    (enum : Fin n ≃ HeavyAction (graph G) (heavySet (graphMass G g) b)) :
    SparseIntegerLaw (Finset (HeavyAction (graph G) (heavySet (graphMass G g) b))) :=
  let m := graphMass G g
  let H := heavySet m b
  let D := heavy (graph G) H
  let q := fun e => bias m p φ (heavyParent (graph G) H e)
  SparseEnumeratedBatch.law enum (balanced D Δ) (conflicts D Δ) p q
    ⟨hp,(by have hh := mul_nonneg hp hφ; nlinarith only [hh,hupper])⟩
    (fun e => bias_probability m hp hφ hupper (heavyParent (graph G) H e))

theorem proposal_eq (G : I → Finset I) (Δ : ℕ) (g β p φ : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1) {n : ℕ}
    (enum : Fin n ≃ HeavyAction (graph G) (heavySet (graphMass G g) β))
    (hpp : 0 ≤ p ∧ p ≤ 1)
    (hq : ∀ e : HeavyAction (graph G) (heavySet (graphMass G g) β),
      0 ≤ bias (graphMass G g) p φ (heavyParent (graph G) _ e) ∧
      bias (graphMass G g) p φ (heavyParent (graph G) _ e) ≤ 1) :
    proposal G Δ g β p φ hp hφ hupper enum =
      SparseEnumeratedBatch.law enum
        (balancedActions (heavyActions (graphActions G) (heavySet (graphMass G g) β)) Δ)
        (balancedConflicts (heavyActions (graphActions G) (heavySet (graphMass G g) β)) Δ)
        p (fun e => bias (graphMass G g) p φ (heavyParent (graph G) _ e)) hpp hq := by
  unfold proposal
  dsimp only
  congr 1
  funext e
  exact conflicts_eq _ _ e

end MetricKMedian.RationalBatchData
end
end

end OAI
