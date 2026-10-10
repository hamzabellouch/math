import OAI.Probability.InvariantIsing.Core.LevyMapDistance
import OAI.Probability.InvariantIsing.Spectral.CompactSpectralClipping
import OAI.Probability.InvariantIsing.Spectral.SpectralExcess

namespace OAI

/-! The finite spectral clipping moves the empirical law by at most its edge excess. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

theorem empirical_clipping_distance {N : ℕ} (hN : 0 < N) (eig : Fin N → ℝ)
    {R : ℝ} (hR : 0 ≤ R) :
    dist (LevyProkhorov.ofMeasure (empiricalSpectralLaw hN eig))
      (LevyProkhorov.ofMeasure ((empiricalSpectralLaw hN eig).map (spectralClip 0 R))) ≤
        spectralExcess eig 0 R := by
  let μ := empiricalSpectralLaw hN eig
  have hh : ∀ᵐ x ∂(μ : Measure ℝ), dist (id x) (spectralClip 0 R x) ≤ spectralExcess eig 0 R := by
    apply ae_finiteSpectralMeasure
    intro i
    rw [Real.dist_eq,abs_sub_comm]
    exact spectralClip_close hR (spectralExcess_nonneg _ _ _) (spectralExcess_bounds eig 0 R i)
  have h := levyProkhorov_map_dist_le_ae (μ : Measure ℝ) id (spectralClip 0 R)
    measurable_id (continuous_spectralClip 0 R).measurable (spectralExcess_nonneg _ _ _) hh
  rw [Measure.map_id] at h
  exact h

end InvariantIsing

end

end OAI
