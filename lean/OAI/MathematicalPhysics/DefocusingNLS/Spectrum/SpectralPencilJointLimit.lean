import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPencilLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeakJointLimit

namespace OAI

/-! Joint convergence of coefficient loads survives the observed inverse. -/

open Filter Topology
namespace DefocusingNLS.SpectralPenaltyFamily
variable {R l : ℝ}

theorem compactPencil_joint_tendsto (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hl : 0 < l) (hlR : l < R) (z : ℂ)
    (K : ℕ × ℂ → SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (K₀ : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (hK : Tendsto K (atTop ×ˢ 𝓝 z) (𝓝 K₀)) :
    Tendsto (fun p : ℕ × ℂ => s.compactPencil ell (hl.trans hlR) p.1 (K p))
      (atTop ×ˢ 𝓝 z) (𝓝 (s.limitPencil ell hl hlR K₀)) := by
  let : NormedAddCommGroup (SpectralHarmonicPair ell R) := inferInstance
  let : NormedSpace ℂ (SpectralHarmonicPair ell R) := inferInstance
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  change Tendsto (fun p : ℕ × ℂ => (s.observedComplexInverse ell (hl.trans hlR) p.1).comp (K p))
    (atTop ×ˢ 𝓝 z) (𝓝 ((s.observedComplexLimit ell hl hlR).comp K₀))
  exact spectralComposition_tendsto_filter (atTop ×ˢ 𝓝 z) _ _ _ _
    ((s.observedComplexInverse_tendsto ell hl hlR).comp tendsto_fst) hK

end DefocusingNLS.SpectralPenaltyFamily

end OAI
