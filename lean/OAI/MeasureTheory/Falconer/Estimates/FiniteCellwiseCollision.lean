import OAI.MeasureTheory.Falconer.Measures.CellwiseCollisionPruning
import OAI.MeasureTheory.Falconer.Measures.FiniteRelativePruning

namespace OAI

/-! # Finite families of local collision prunings with their original cell weights -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*}

theorem cellwise_collision_pruning_of_exists (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [SFinite ν]
    (I : Finset ι) (Q : ι → Set (Space d))
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hpos : ∀ i ∈ I, μ (Q i) ≠ 0)
    (hdisj : (I : Set ι).PairwiseDisjoint Q)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (δ : ℝ) (F : ι → ℝ≥0∞) (cost : ℝ≥0∞)
    (hlocal : ∀ i ∈ I, ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      ((ProbabilityTheory.cond μ (Q i)).prod ν) ((G ∩ (Q i ×ˢ univ)) \ H) ≤ cost ∧
      ∀ p ∈ H, radialCollisionMass (ProbabilityTheory.cond μ (Q i)) δ p ≤ F i) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
      (μ.prod ν) (G \ H) ≤ cost*μ univ ∧
      ∀ i ∈ I, ∀ p ∈ H, p.1 ∈ Q i →
        radialCollisionMass (ProbabilityTheory.cond μ (Q i)) δ p ≤ F i := by
  classical
  have hex : ∀ i, ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      (i ∈ I → ((ProbabilityTheory.cond μ (Q i)).prod ν)
        ((G ∩ (Q i ×ˢ univ)) \ H) ≤ cost ∧
        ∀ p ∈ H, radialCollisionMass (ProbabilityTheory.cond μ (Q i)) δ p ≤ F i) := by
    intro i
    by_cases hi : i ∈ I
    · obtain ⟨H,hH,hcost,hbound⟩ := hlocal i hi
      exact ⟨H,hH,fun _ => ⟨hcost,hbound⟩⟩
    · exact ⟨∅,MeasurableSet.empty,fun h => (hi h).elim⟩
  choose H hH hrest using hex
  exact cellwise_radial_collision_pruning μ ν I Q hQ hpos hdisj G hG H (fun i _ => hH i)
    δ F cost (fun i hi => (hrest i hi).1) (fun i hi => (hrest i hi).2)

theorem finite_cellwise_collision_pruning (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [SFinite ν]
    (J : ℕ) (I : ℕ → Finset ι) (Q : ℕ → ι → Set (Space d))
    (hQ : ∀ j < J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hpos : ∀ j < J, ∀ i ∈ I j, μ (Q j i) ≠ 0)
    (hdisj : ∀ j < J, (I j : Set ι).PairwiseDisjoint (Q j))
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (δ : ℕ → ℝ) (F : ℕ → ι → ℝ≥0∞) (cost : ℕ → ℝ≥0∞)
    (hlocal : ∀ j < J, ∀ i ∈ I j, ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      ((ProbabilityTheory.cond μ (Q j i)).prod ν) ((G ∩ (Q j i ×ˢ univ)) \ H) ≤ cost j ∧
      ∀ p ∈ H, radialCollisionMass (ProbabilityTheory.cond μ (Q j i)) (δ j) p ≤ F j i) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
      (μ.prod ν) (G \ H) ≤ ∑ j ∈ Finset.range J, cost j*μ univ ∧
      ∀ j < J, ∀ i ∈ I j, ∀ p ∈ H, p.1 ∈ Q j i →
        radialCollisionMass (ProbabilityTheory.cond μ (Q j i)) (δ j) p ≤ F j i := by
  have hlevels : ∀ j < J, ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
      (μ.prod ν) (G \ H) ≤ cost j*μ univ ∧
      ∀ p ∈ H, ∀ i ∈ I j, p.1 ∈ Q j i →
        radialCollisionMass (ProbabilityTheory.cond μ (Q j i)) (δ j) p ≤ F j i := by
    intro j hj
    obtain ⟨H,hH,hHG,hcost,hbound⟩ := cellwise_collision_pruning_of_exists μ ν (I j) (Q j)
      (hQ j hj) (hpos j hj) (hdisj j hj) G hG (δ j) (F j) (cost j) (hlocal j hj)
    exact ⟨H,hH,hHG,hcost,fun p hp i hi hpQ => hbound i hi p hp hpQ⟩
  obtain ⟨H,hH,hHG,hcost,hbound⟩ := finite_relative_pruning (μ.prod ν) G hG J
    (fun j => cost j*μ univ) (fun j p => ∀ i ∈ I j, p.1 ∈ Q j i →
      radialCollisionMass (ProbabilityTheory.cond μ (Q j i)) (δ j) p ≤ F j i) hlevels
  exact ⟨H,hH,hHG,hcost,fun j hj i hi p hp hpQ => hbound j hj p hp i hi hpQ⟩

end Falconer

end OAI
