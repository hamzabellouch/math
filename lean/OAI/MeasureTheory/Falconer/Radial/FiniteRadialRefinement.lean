import OAI.MeasureTheory.Falconer.Radial.TwoSidedRadialIntersection

namespace OAI

/-! # Intersecting finitely many two-sided radial refinements -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ}

theorem finite_radial_refinement (μ ν : Measure (Space d))
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (I : Finset ℕ) (cost bound : ℕ → ℝ≥0∞) (radius : ℕ → ℝ)
    (hlocal : ∀ j ∈ I, ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
      (μ.prod ν) (G \ H) ≤ cost j ∧
      (∀ x u : Space d, μ {z | (z,x) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ radius j} ≤ bound j) ∧
      (∀ z u : Space d, ν {x | (z,x) ∈ H ∧ ‖normalize (x-z)-u‖ ≤ radius j} ≤ bound j)) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
      (μ.prod ν) (G \ H) ≤ ∑ j ∈ I, cost j ∧
      ∀ j ∈ I,
        (∀ x u : Space d, μ {z | (z,x) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ radius j} ≤ bound j) ∧
        (∀ z u : Space d, ν {x | (z,x) ∈ H ∧ ‖normalize (x-z)-u‖ ≤ radius j} ≤ bound j) := by
  classical
  have hex : ∀ j : ℕ, ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      (j ∈ I → H ⊆ G ∧ (μ.prod ν) (G \ H) ≤ cost j ∧
        (∀ x u : Space d, μ {z | (z,x) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ radius j} ≤ bound j) ∧
        (∀ z u : Space d, ν {x | (z,x) ∈ H ∧ ‖normalize (x-z)-u‖ ≤ radius j} ≤ bound j)) := by
    intro j
    by_cases hj : j ∈ I
    · obtain ⟨H,hH,hsub,hd,hc⟩ := hlocal j hj
      exact ⟨H,hH,fun _ => ⟨hsub,hd,hc⟩⟩
    · exact ⟨G,hG,fun h => (hj h).elim⟩
  choose H hH hrest using hex
  let B := ⋃ j ∈ I, G \ H j
  let K := G \ B
  have hK : MeasurableSet K := hG.diff (Finset.measurableSet_biUnion I (fun j _ => hG.diff (hH j)))
  have hsub (j : ℕ) (hj : j ∈ I) : K ⊆ H j := by
    intro z hz
    by_contra hn
    exact hz.2 (mem_iUnion₂.mpr ⟨j,hj,hz.1,hn⟩)
  refine ⟨K,hK,sdiff_subset,?_,?_⟩
  · have hdiff : G \ K ⊆ B := by
      intro z hz
      by_contra hn
      exact hz.2 ⟨hz.1,hn⟩
    exact (measure_mono hdiff).trans ((measure_biUnion_finset_le _ _).trans
      (Finset.sum_le_sum (fun j hj => (hrest j hj).2.1)))
  · intro j hj
    refine ⟨?_,?_⟩
    · intro x u
      apply le_trans _ ((hrest j hj).2.2.1 x u)
      exact measure_mono (fun _ hz => ⟨hsub j hj hz.1,hz.2⟩)
    · intro z u
      apply le_trans _ ((hrest j hj).2.2.2 z u)
      exact measure_mono (fun _ hz => ⟨hsub j hj hz.1,hz.2⟩)

end Falconer

end OAI
