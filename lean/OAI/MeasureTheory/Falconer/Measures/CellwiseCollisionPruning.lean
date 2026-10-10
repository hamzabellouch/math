import OAI.MeasureTheory.Falconer.Estimates.CellwisePairDeletion
import OAI.MeasureTheory.Falconer.Radial.RadialCollisionMass

namespace OAI

/-! # Combining conditional-cell radial pruning with the original source weights -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ} {ι : Type*}

theorem cellwise_radial_collision_pruning (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [SFinite ν]
    (I : Finset ι) (Q : ι → Set (Space d))
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hpos : ∀ i ∈ I, μ (Q i) ≠ 0)
    (hdisj : (I : Set ι).PairwiseDisjoint Q)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (H : ι → Set (Space d × Space d)) (hH : ∀ i ∈ I, MeasurableSet (H i))
    (δ : ℝ) (F : ι → ℝ≥0∞) (cost : ℝ≥0∞)
    (hcost : ∀ i ∈ I, ((ProbabilityTheory.cond μ (Q i)).prod ν)
      ((G ∩ (Q i ×ˢ univ)) \ H i) ≤ cost)
    (hlocal : ∀ i ∈ I, ∀ p ∈ H i,
      radialCollisionMass (ProbabilityTheory.cond μ (Q i)) δ p ≤ F i) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ cost*μ univ ∧
      ∀ i ∈ I, ∀ p ∈ G', p.1 ∈ Q i →
        radialCollisionMass (ProbabilityTheory.cond μ (Q i)) δ p ≤ F i := by
  classical
  let E := fun i => (G ∩ (Q i ×ˢ univ)) \ H i
  let D := ⋃ i ∈ I, E i ∩ (Q i ×ˢ univ)
  have hE : ∀ i ∈ I, MeasurableSet (E i) := fun i hi =>
    (hG.inter ((hQ i hi).prod MeasurableSet.univ)).diff (hH i hi)
  have hD : MeasurableSet D := Finset.measurableSet_biUnion I
    (fun i hi => (hE i hi).inter ((hQ i hi).prod MeasurableSet.univ))
  refine ⟨G \ D,hG.diff hD,sdiff_subset,?_,?_⟩
  · apply (measure_mono _).trans
      (conditional_cellwise_pair_deletion μ ν I Q E hQ hE hpos hdisj cost hcost)
    intro p hp
    by_contra hn
    exact hp.2 ⟨hp.1,hn⟩
  · intro i hi p hp hpQ
    apply hlocal i hi p
    by_contra hn
    apply hp.2
    exact mem_iUnion₂.mpr ⟨i,hi,⟨⟨⟨hp.1,hpQ,mem_univ _⟩,hn⟩,hpQ,mem_univ _⟩⟩

end Falconer

end OAI
