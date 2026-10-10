import OAI.Analysis.KadisonKastler.StateActionStates
import OAI.Analysis.KadisonKastler.StateActionFubini
import OAI.Analysis.KadisonKastler.PoissonNormContinuity

namespace OAI

/-! # Strongly invariant states by Poisson smoothing

This proves the smoothing step of Marrakchi, arXiv:1811.10253v2,
Proposition 3.10. Preservation of a prescribed nonnormal restriction is
only asserted here on operators whose orbits are norm continuous.
-/

namespace KadisonKastler

open MeasureTheory NaimarkZFC

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem poissonActionAverage_orbit_continuous (a : H →L[ℂ] H) :
    Continuous (stateActionOrbit U
      (stateActionAverage U hU (ProbabilityTheory.cauchyMeasure 0 1) a)) := by
  have he (s : ℝ) :
      stateActionOrbit U (stateActionAverage U hU (ProbabilityTheory.cauchyMeasure 0 1) a) s =
        poissonVectorAverage (stateActionOrbit U a)
          (stateActionOrbit_continuous U hU a) ‖a‖
          (fun t => (stateActionOrbit_norm U a t).le) s 1 := by
    ext x
    rw [stateActionOrbit_average_apply]
    change (∫ t, stateActionOrbit U a (s+t) x ∂ProbabilityTheory.cauchyMeasure 0 1)=
      ∫ t, stateActionOrbit U a (s+1*t) x ∂ProbabilityTheory.cauchyMeasure 0 1
    simp only [one_mul]
  change Continuous (fun s : ℝ =>
    stateActionOrbit U (stateActionAverage U hU (ProbabilityTheory.cauchyMeasure 0 1) a) s)
  simp_rw [he]
  exact continuous_poissonVectorAverage (stateActionOrbit U a)
    (stateActionOrbit_continuous U hU a) (norm_nonneg a)
    (fun t => (stateActionOrbit_norm U a t).le) (by norm_num)

theorem exists_strongly_invariant_state
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ)
    (hinv : ∀ t a, φ (stateActionOrbit U a t)=φ a) :
    ∃ ψ : (H →L[ℂ] H) →L[ℂ] ℂ, IsState ψ ∧
      (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : H →L[ℂ] H),
        ψ (stateActionAverage U hU μ a)=ψ a) ∧
      (∀ (a : H →L[ℂ] H), Continuous (stateActionOrbit U a) → ψ a=φ a) := by
  let ν := ProbabilityTheory.cauchyMeasure 0 1
  let ψ := φ.comp (stateActionAverageMap U hU ν)
  refine ⟨ψ,state_comp_actionAverage U hU ν φ hφ,?_,?_⟩
  · intro μ hμ a
    change φ (stateActionAverage U hU ν (stateActionAverage U hU μ a))=
      φ (stateActionAverage U hU ν a)
    rw [stateActionAverage_commute U hU ν μ a]
    exact invariant_functional_actionAverage U hU φ hinv μ _
      (poissonActionAverage_orbit_continuous U hU a)
  · intro a ha
    exact invariant_functional_actionAverage U hU φ hinv ν a ha

end

end KadisonKastler

end OAI
