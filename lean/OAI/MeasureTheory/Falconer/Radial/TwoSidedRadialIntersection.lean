import OAI.MeasureTheory.Falconer.Estimates.NonendpointOneScale

namespace OAI

/-! # Combining the two original orientations without normalizing pair fibers -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem intersect_radial_orientations (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (G H K : Set (Space d × Space d)) (hG : MeasurableSet G)
    (hH : MeasurableSet H) (hK : MeasurableSet K)
    (hHG : H ⊆ G) (_hKG : K ⊆ Prod.swap ⁻¹' G)
    {a b C r : ℝ≥0∞} {δ : ℝ}
    (hHcost : (μ.prod ν) (G \ H) ≤ a)
    (hKcost : (ν.prod μ) ((Prod.swap ⁻¹' G) \ K) ≤ b)
    (hHcap : ∀ x u : Space d, μ {z | (z,x) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ δ} ≤ C)
    (hKcap : ∀ z u : Space d, ν {x | (x,z) ∈ K ∧ ‖normalize (x-z)-u‖ ≤ δ} ≤ r) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ a+b ∧
      (∀ x u : Space d, μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ δ} ≤ C) ∧
      (∀ z u : Space d, ν {x | (z,x) ∈ G' ∧ ‖normalize (x-z)-u‖ ≤ δ} ≤ r) := by
  let G' := H ∩ (Prod.swap ⁻¹' K)
  refine ⟨G',hH.inter (hK.preimage measurable_swap),fun z hz => hHG hz.1,?_,?_,?_⟩
  · have hsub : G \ G' ⊆ (G \ H) ∪ (Prod.swap ⁻¹' ((Prod.swap ⁻¹' G) \ K)) := by
      intro z hz
      by_cases hh : z ∈ H
      · right
        exact ⟨hz.1,fun hk => hz.2 ⟨hh,hk⟩⟩
      · exact Or.inl ⟨hz.1,hh⟩
    apply (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    apply add_le_add hHcost
    rw [← Measure.map_apply measurable_swap ((hG.preimage measurable_swap).diff hK),Measure.prod_swap]
    exact hKcost
  · intro x u
    apply le_trans _ (hHcap x u)
    exact measure_mono (fun _ hz => ⟨hz.1.1,hz.2⟩)
  · intro z u
    apply le_trans _ (hKcap z u)
    exact measure_mono (fun _ hz => ⟨hz.1.2,hz.2⟩)

end Falconer

end OAI
