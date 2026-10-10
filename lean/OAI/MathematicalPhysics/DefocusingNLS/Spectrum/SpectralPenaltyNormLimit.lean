import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPenaltyObservationLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralDualWeakSubsequence
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOperatorNormCriterion

namespace OAI

/-! The pressure-penalized inverse converges in norm after compact observation,
as required by the constrained compact pencil. -/

open Set MeasureTheory Filter Topology
open scoped ENNReal
namespace DefocusingNLS
namespace SpectralPenaltyFamily
variable {R l : ℝ}

noncomputable def observedInverse (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hR : 0 < R) (n : ℕ) :
    StrongDual ℝ (SpectralHarmonicPair ell R) →L[ℝ] SpectralRadialObservationSpace R :=
  ((spectralHarmonicObservation ell R hR).restrictScalars ℝ).comp (s.inverse ell n)

noncomputable def observedLimitInverse (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hR : 0 < R) :
    StrongDual ℝ (SpectralHarmonicPair ell R) →L[ℝ] SpectralRadialObservationSpace R :=
  ((spectralHarmonicObservation ell R hR).restrictScalars ℝ).comp (s.limitInverse ell)

theorem observedInverse_tendsto (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hl : 0 < l) (hlR : l < R) :
    Tendsto (s.observedInverse ell (hl.trans hlR)) atTop
      (𝓝 (s.observedLimitInverse ell (hl.trans hlR))) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : TopologicalSpace.SeparableSpace (SpectralHarmonicPair ell R) :=
    spectralHarmonicPair_separable ell R
  refine spectralOperatorNorm_criterion (E := StrongDual ℝ (SpectralHarmonicPair ell R))
    (Z := SpectralRadialObservationSpace R)
    (s.observedInverse ell (hl.trans hlR)) (s.observedLimitInverse ell (hl.trans hlR)) ?_ ?_ ?_
  · intro F hF
    obtain ⟨F₀,_,φ,hφ,hw⟩ := spectralRealHilbert_dual_weak_subsequence F 1 hF
    exact ⟨F₀,φ,hφ,hw⟩
  · intro ns hns F F₀ hF hw
    exact (s.reindex ns hns).observation_tendsto ell hl hlR F F₀ 1 hF
      (fun v => hw (ContinuousLinearMap.apply ℝ ℝ v))
  · intro F F₀ hF hw
    exact spectralHarmonicCoreInverse_weak_input ell R l (hl.trans hlR)
      s.limitWeight s.lower s.lower_pos s.limit_radial_lower s.limit_angular_lower
      F F₀ 1 hF hw

end SpectralPenaltyFamily
end DefocusingNLS

end OAI
