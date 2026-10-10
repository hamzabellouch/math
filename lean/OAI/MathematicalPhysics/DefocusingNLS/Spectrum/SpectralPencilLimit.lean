import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCompactPencil

namespace OAI

/-! Compactness and holomorphy also hold for the constrained limiting pencil. -/

open Filter Topology
namespace DefocusingNLS.SpectralPenaltyFamily
variable {R l : ℝ}

theorem limitPencil_compact (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hl : 0 < l) (hlR : l < R)
    (K : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R) :
    IsCompactOperator (s.limitPencil ell hl hlR K) := by
  let : NormedAddCommGroup (SpectralHarmonicPair ell R) := inferInstance
  let : NormedSpace ℂ (SpectralHarmonicPair ell R) := inferInstance
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  apply isCompactOperator_of_tendsto
    (s.compactPencil_tendsto ell hl hlR (fun _ => K) K tendsto_const_nhds)
  exact Eventually.of_forall (fun n => s.compactPencil_compact ell (hl.trans hlR) n K)

noncomputable local instance coefficientSpaceNormed (ell : ℕ) (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R) := by
  let : NormedAddCommGroup (SpectralHarmonicPair ell R) := inferInstance
  let : NormedSpace ℂ (SpectralHarmonicPair ell R) := inferInstance
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance pencilSpaceNormed (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R) := by
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem limitPencil_analyticAt (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hl : 0 < l) (hlR : l < R)
    (K : ℂ → SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (z : ℂ) (hK : AnalyticAt ℂ K z) :
    AnalyticAt ℂ (fun w => s.limitPencil ell hl hlR (K w)) z := by
  let L := ContinuousLinearMap.compL ℂ (SpectralRadialObservationSpace R)
    (SpectralHarmonicPair ell R) (SpectralRadialObservationSpace R)
      (s.observedComplexLimit ell hl hlR)
  exact (L.analyticAt (K z)).comp hK

end DefocusingNLS.SpectralPenaltyFamily

end OAI
