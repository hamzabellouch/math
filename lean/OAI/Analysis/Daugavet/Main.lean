import OAI.Analysis.Daugavet.LimitingSlices

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace ExactModuli

theorem kadets_werner_existence :
    ∃ E : Submodule ℝ (Lp ℝ 1 kwMeasure),
      IsClosed (E : Set (Lp ℝ 1 kwMeasure)) ∧ (¬ FiniteDimensional ℝ E) ∧
      MeasurePrecompactBall kwMeasure E ∧ UnitSliceProperty E ∧ Daugavet E := by
  exact ⟨KW.constructedSpace, KW.constructedSpace_closed, KW.constructedSpace_infiniteDimensional,
    KW.constructedSpace_measurePrecompact, KW.constructedSpace_unitSlice, KW.constructedSpace_daugavet⟩

end ExactModuli

namespace ExactModuli

theorem exact_example :
    ∃ E : Submodule ℝ (Lp ℝ 1 kwMeasure),
      IsClosed (E : Set (Lp ℝ 1 kwMeasure)) ∧ (¬ FiniteDimensional ℝ E) ∧
      MeasurePrecompactBall kwMeasure E ∧ UnitSliceProperty E ∧ Daugavet E ∧
      (∀ (x : E), ‖x‖ = 1 → ∀ t : ℝ, 0 < t →
        H (normSeminorm ℝ E) x t = max (t / 2) (t - 1) ∧
        D (normSeminorm ℝ E) x t = max 0 (t - 2)) ∧
      (∀ t : ℝ, 0 < t →
        averagedModulus (normSeminorm ℝ E) t = max (t / 2) (t - 1) ∧
        oneSidedModulus (normSeminorm ℝ E) t = max 0 (t - 2)) ∧
      (∀ N : Seminorm ℝ E, EquivalentNorm N → ¬ AUC N) := by
  let := KW.kwMeasure_probability
  obtain ⟨E,hclosed,hdim,hcompact,hslice,hdaugavet⟩ := kadets_werner_existence
  obtain ⟨hpoint,hcenters,hrenorm⟩ := exact_main kwMeasure E hclosed hdim hcompact hdaugavet
  exact ⟨E,hclosed,hdim,hcompact,hslice,hdaugavet,hpoint,hcenters,hrenorm⟩

end ExactModuli

end

end OAI
