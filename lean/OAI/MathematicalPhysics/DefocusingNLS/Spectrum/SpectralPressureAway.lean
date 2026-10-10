import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicPenalty
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicWeightDifference

namespace OAI

/-! Pressure terms tested away from the core are controlled by the exterior coefficient. -/

open Set MeasureTheory Filter Topology
namespace DefocusingNLS

theorem spectralWeightedPressure_symmetric (R : ℝ) (w : SpectralHarmonicWeight R)
    (p : ℝ → ℝ) (hpm : AEStronglyMeasurable p (radialPressureMeasure R))
    (hpb : ∀ᵐ r ∂radialPressureMeasure R, ‖p r‖ ≤ 1) (u v : SpectralRadialL2 R) :
    inner ℝ (spectralWeightedPressure R w p hpm hpb u) v=
      inner ℝ u (spectralWeightedPressure R w p hpm hpb v) := by
  change (∫ r, inner ℝ (spectralWeightedPressure R w p hpm hpb u r) (v r)
    ∂radialPressureMeasure R)=∫ r, inner ℝ (u r) (spectralWeightedPressure R w p hpm hpb v r)
      ∂radialPressureMeasure R
  apply integral_congr_ae
  filter_upwards [spectralL2Weight_ae (radialPressureMeasure R) (fun r => w.density r*p r)
      (w.radial_measurable.mul hpm) w.bound (weightedPressure_bound R w p hpb) u,
    spectralL2Weight_ae (radialPressureMeasure R) (fun r => w.density r*p r)
      (w.radial_measurable.mul hpm) w.bound (weightedPressure_bound R w p hpb) v] with r hu hv
  change spectralWeightedPressure R w p hpm hpb u r=(w.density r*p r) • u r at hu
  change spectralWeightedPressure R w p hpm hpb v r=(w.density r*p r) • v r at hv
  rw [hu,hv,real_inner_smul_left,real_inner_smul_right]

theorem spectralWeightedPressure_offCore_norm (R L a η : ℝ) (w : SpectralHarmonicWeight R)
    (p : ℝ → ℝ) (hpm : AEStronglyMeasurable p (radialPressureMeasure R))
    (hpb : ∀ᵐ r ∂radialPressureMeasure R, ‖p r‖ ≤ 1)
    (hext : ∀ᵐ r ∂radialPressureMeasure R, L < r → ‖a⁻¹*(w.density r*p r)‖ ≤ η)
    (v : SpectralRadialL2 R) (hv : (fun r => v r) =ᵐ[(radialPressureMeasure R).restrict (Iic L)] 0) :
    ‖a⁻¹ • spectralWeightedPressure R w p hpm hpb v‖ ≤ η*‖v‖ := by
  have hcore : ∀ᵐ r ∂radialPressureMeasure R, r ≤ L → v r=0 := by
    simpa only [mem_Iic,Pi.zero_apply] using (ae_restrict_iff' measurableSet_Iic).mp hv
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_smul a⁻¹ (spectralWeightedPressure R w p hpm hpb v),
    spectralL2Weight_ae (radialPressureMeasure R) (fun r => w.density r*p r)
      (w.radial_measurable.mul hpm) w.bound (weightedPressure_bound R w p hpb) v,
    hcore,hext] with r hs hpv hc he
  change spectralWeightedPressure R w p hpm hpb v r=(w.density r*p r) • v r at hpv
  rw [hs,Pi.smul_apply,hpv,smul_smul,norm_smul]
  by_cases hr : r ≤ L
  · simp only [hc hr,norm_zero,mul_zero,le_refl]
  · exact mul_le_mul_of_nonneg_right (he (lt_of_not_ge hr)) (norm_nonneg _)

theorem spectralWeightedPressure_offCore_inner (R L a η : ℝ) (w : SpectralHarmonicWeight R)
    (p : ℝ → ℝ) (hpm : AEStronglyMeasurable p (radialPressureMeasure R))
    (hpb : ∀ᵐ r ∂radialPressureMeasure R, ‖p r‖ ≤ 1)
    (hext : ∀ᵐ r ∂radialPressureMeasure R, L < r → ‖a⁻¹*(w.density r*p r)‖ ≤ η)
    (u v : SpectralRadialL2 R) (hv : (fun r => v r) =ᵐ[(radialPressureMeasure R).restrict (Iic L)] 0) :
    ‖a⁻¹*inner ℝ (spectralWeightedPressure R w p hpm hpb u) v‖ ≤ ‖u‖*(η*‖v‖) := by
  rw [spectralWeightedPressure_symmetric,← real_inner_smul_right]
  exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans (mul_le_mul_of_nonneg_left
    (spectralWeightedPressure_offCore_norm R L a η w p hpm hpb hext v hv) (norm_nonneg _))

end DefocusingNLS

end OAI
