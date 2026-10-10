import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralObservedComplexLimit
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Operator.NormedSpace

namespace OAI

/-! The compact analytic pencil produced by the weighted pressure inverse. -/

open Filter Topology
namespace DefocusingNLS
theorem spectralComposition_tendsto {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (T : ℕ → F →L[ℂ] G) (T₀ : F →L[ℂ] G)
    (K : ℕ → E →L[ℂ] F) (K₀ : E →L[ℂ] F)
    (hT : Tendsto T atTop (𝓝 T₀)) (hK : Tendsto K atTop (𝓝 K₀)) :
    Tendsto (fun n => (T n).comp (K n)) atTop (𝓝 (T₀.comp K₀)) := by
  exact ((ContinuousLinearMap.compL ℂ E F G).continuous₂.continuousAt.tendsto).comp
    (hT.prodMk_nhds hK)

namespace SpectralPenaltyFamily
variable {R l : ℝ}

noncomputable def compactPencil (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hR : 0 < R) (n : ℕ)
    (K : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R) :
    SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R :=
  (s.observedComplexInverse ell hR n).comp K

noncomputable def limitPencil (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hl : 0 < l) (hlR : l < R)
    (K : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R) :
    SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R :=
  (s.observedComplexLimit ell hl hlR).comp K

theorem compactPencil_compact (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hR : 0 < R) (n : ℕ)
    (K : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R) :
    IsCompactOperator (s.compactPencil ell hR n K) := by
  exact (spectralHarmonicObservation_compact ell R hR).comp_clm
    ((spectralHarmonicPenaltyInverseComplex ell R (s.weight n) s.lower s.lower_pos
      (s.radial_lower n) (s.angular_lower n) (s.pressure n) (s.pressure_measurable n)
      (s.pressure_bound n) (s.pressure_nonneg n) (s.scale n) (s.scale_pos n)).comp K)

theorem compactPencil_tendsto (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hl : 0 < l) (hlR : l < R)
    (K : ℕ → SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (K₀ : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (hK : Tendsto K atTop (𝓝 K₀)) :
    Tendsto (fun n => s.compactPencil ell (hl.trans hlR) n (K n)) atTop
      (𝓝 (s.limitPencil ell hl hlR K₀)) := by
  let : NormedAddCommGroup (SpectralHarmonicPair ell R) := inferInstance
  let : NormedSpace ℂ (SpectralHarmonicPair ell R) := inferInstance
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  change Tendsto (fun n => (s.observedComplexInverse ell (hl.trans hlR) n).comp (K n))
    atTop (𝓝 ((s.observedComplexLimit ell hl hlR).comp K₀))
  exact spectralComposition_tendsto (E := SpectralRadialObservationSpace R)
    (F := SpectralHarmonicPair ell R) (G := SpectralRadialObservationSpace R)
    _ _ K K₀ (s.observedComplexInverse_tendsto ell hl hlR) hK

noncomputable local instance spectralCoefficientSpaceNormed (ell : ℕ) (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R) := by
  letI : NormedAddCommGroup (SpectralHarmonicPair ell R) := inferInstance
  letI : NormedSpace ℂ (SpectralHarmonicPair ell R) := inferInstance
  letI : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  letI : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance spectralPencilSpaceNormed (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R) := by
  letI : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  letI : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem compactPencil_analyticAt (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hR : 0 < R) (n : ℕ)
    (K : ℂ → SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (z : ℂ) (hK : AnalyticAt ℂ K z) :
    AnalyticAt ℂ (fun w => s.compactPencil ell hR n (K w)) z := by
  let L := ContinuousLinearMap.compL ℂ (SpectralRadialObservationSpace R)
    (SpectralHarmonicPair ell R) (SpectralRadialObservationSpace R)
      (s.observedComplexInverse ell hR n)
  exact (L.analyticAt (K z)).comp hK

end SpectralPenaltyFamily
end DefocusingNLS

end OAI
