import OAI.MeasureTheory.Falconer.Estimates.TroublesomePair

namespace OAI

/-! # Intersecting the actual pair sets at finitely many radial scales -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ}

theorem finite_radial_scale_intersection (μ ν : Measure (Space d))
    (I : Finset ℕ) (G : ℕ → Set (Space d × Space d))
    (t C : ℕ → ℝ≥0∞) (r : ℕ → ℝ)
    (hG : ∀ j ∈ I, MeasurableSet (G j))
    (hcost : ∀ j ∈ I, (ν.prod μ) (G j)ᶜ ≤ t j)
    (hcap : ∀ j ∈ I, ∀ x u : Space d,
      μ {z | (x,z) ∈ G j ∧ ‖normalize (z-x)-u‖ ≤ r j} ≤ C j) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      (ν.prod μ) Hᶜ ≤ ∑ j ∈ I, t j ∧
      ∀ j ∈ I, ∀ s : ℝ, s ≤ r j → ∀ x u : Space d,
        μ {z | (x,z) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ s} ≤ C j := by
  classical
  let H := ⋂ j ∈ I, G j
  have hm : MeasurableSet H := Finset.measurableSet_biInter I hG
  refine ⟨H,hm,?_,?_⟩
  · have he : Hᶜ = ⋃ j ∈ I, (G j)ᶜ := by
      ext p
      simp only [H,mem_compl_iff,mem_iInter,mem_iUnion]
      push Not
      constructor <;> rintro ⟨j,hj,hp⟩ <;> exact ⟨j,hj,hp⟩
    rw [he]
    exact (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum hcost)
  · intro j hj s hs x u
    apply (measure_mono ?_).trans (hcap j hj x u)
    intro z hz
    exact ⟨mem_iInter₂.mp hz.1 j hj,hz.2.trans hs⟩

end Falconer

end OAI
