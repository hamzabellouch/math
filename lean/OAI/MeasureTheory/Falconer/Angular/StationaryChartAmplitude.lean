import OAI.MeasureTheory.Falconer.Angular.StationaryChartCutoffs
import OAI.MeasureTheory.Falconer.Estimates.SmoothCompositionScale
import OAI.MeasureTheory.Falconer.Angular.CompactStationaryAmplitude

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff SchwartzMap

noncomputable def stationaryAmplitude (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  (stationaryWeight u : ℂ) * f (extendedStationaryInverse u)

 theorem stationaryAmplitude_eq {u : ℝ} (hu : u ∈ Icc (-1:ℝ) 1) (f : ℝ → ℂ) :
    stationaryAmplitude f u =
      (stationarySineJacobian u : ℂ) * (stationaryCutoff u : ℂ) * f (stationarySineInverse u) := by
  simp only [stationaryAmplitude,stationaryWeight,Complex.ofReal_mul,extendedStationaryInverse_eq hu]
  ring

 theorem stationaryAmplitude_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (stationaryAmplitude f) := by
  exact (Complex.ofRealCLM.contDiff.comp stationaryWeight_contDiff).mul
    (hf.comp extendedStationaryInverse_contDiff)

 theorem stationaryAmplitude_tsupport (f : ℝ → ℂ) :
    tsupport (stationaryAmplitude f) ⊆ Icc (-1:ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hn
  have hw : stationaryWeight x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hn (stationaryWeight_tsupport h))
  exact hx (by simp [stationaryAmplitude,hw])

 theorem stationaryAmplitude_uniform_derivatives (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ f : ℝ → ℂ, ContDiff ℝ ∞ f →
      ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ k ≤ n, ∀ y, ‖iteratedDeriv k f y‖ ≤ C*D^k) →
      ∀ x, ‖iteratedDeriv n (stationaryAmplitude f) x‖ ≤ A*C*D^n := by
  obtain ⟨A,hA,hbound⟩ := compact_weighted_composition_scale
    (Complex.ofRealCLM.contDiff.comp stationaryWeight_contDiff)
    extendedStationaryInverse_contDiff (K := Icc (-1:ℝ) 1) isCompact_Icc n
  refine ⟨A,hA,?_⟩
  intro f hf C D hC hD hb x
  by_cases hx : x ∈ Icc (-1:ℝ) 1
  · exact hbound f hf C D hC hD hb x hx
  · have he : iteratedDeriv n (stationaryAmplitude f) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hh => hx
        (stationaryAmplitude_tsupport f (complex_iteratedDeriv_tsupport _ n hh)))
    rw [he,norm_zero]
    positivity

 theorem stationaryAmplitude_schwartz {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ∃ φ : 𝓢(ℝ,ℂ), (φ : ℝ → ℂ) = stationaryAmplitude f :=
  compact_smooth_to_schwartz (stationaryAmplitude_tsupport f) (stationaryAmplitude_contDiff hf)

end PlanarFalconer

end OAI
