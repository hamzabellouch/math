import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPencilLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCompactKernelExclusion

namespace OAI

/-! Absence of limiting weak kernels is stable for the actual penalty pencil. -/

open Filter Topology
namespace DefocusingNLS.SpectralPenaltyFamily

theorem compactPencil_eventually_kernel_zero {R L : ℝ}
    (s : SpectralPenaltyFamily R L) (ell : ℕ) (hL : 0 < L) (hLR : L < R)
    (K : ℕ → SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (K₀ : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (hK : Tendsto K atTop (𝓝 K₀))
    (hzero : ∀ v, s.limitPencil ell hL hLR K₀ v=v → v=0) :
    ∀ᶠ n in atTop, ∀ v, s.compactPencil ell (hL.trans hLR) n (K n) v=v → v=0 := by
  let : NormedAddCommGroup (SpectralHarmonicPair ell R) := inferInstance
  let : NormedSpace ℂ (SpectralHarmonicPair ell R) := inferInstance
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact compact_kernel_eventually_zero _ _ (s.compactPencil_tendsto ell hL hLR K K₀ hK)
    (s.limitPencil_compact ell hL hLR K₀) hzero

end DefocusingNLS.SpectralPenaltyFamily

end OAI
