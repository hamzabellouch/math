import OAI.Geometry.RCD.Harmonic.AverageHarmonicSource

namespace OAI

/-! # Fubini for the actual compact integrable cutoff errors -/

open Set Metric MeasureTheory Filter
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk in
/-- Averaging and integration commute for the genuine integrable compact
error density, even when it is not an L2 function. -/
theorem kernelAverage_integral_density {t : ℝ} (ht : 0 < t)
    (A : Set X) (hA : MeasurableSet A) (hbounded : Bornology.IsBounded A)
    {g : X → ℝ} (hg : Integrable g μ) {K : Set X} (hK : IsCompact K)
    (hgzero : ∀ᵐ z ∂μ, z ∉ K → g z = 0) :
    (∫ z, kernelAverage μ ker t A z * g z ∂μ) =
      (μ.real A)⁻¹ * ∫ y in A, ∫ z, ker t y z * g z ∂μ ∂μ := by
  let : IsFiniteMeasure (μ.restrict A) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hbounded.measure_lt_top⟩
  let F := fun yz : X × X => ker t yz.1 yz.2 * g yz.2
  have hcompact : IsCompact (closure A ×ˢ K) :=
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure hbounded.closure).prod hK
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image (hk.continuous_joint t ht).norm.continuousOn
  let D := max C 0
  have hDom : Integrable (fun yz : X × X => D * |g yz.2|) ((μ.restrict A).prod μ) := by
    exact (integrable_const D).mul_prod hg.abs
  have hFm : AEStronglyMeasurable F ((μ.restrict A).prod μ) :=
    (hk.continuous_joint t ht).aestronglyMeasurable.mul hg.aestronglyMeasurable.comp_snd
  have hbound : ∀ᵐ yz ∂(μ.restrict A).prod μ, ‖F yz‖ ≤ D * |g yz.2| := by
    have hAprod := (Measure.quasiMeasurePreserving_fst (μ := μ.restrict A) (ν := μ)).ae (ae_restrict_mem hA)
    have hgprod := (Measure.quasiMeasurePreserving_snd (μ := μ.restrict A) (ν := μ)).ae hgzero
    filter_upwards [hAprod, hgprod] with yz hy hz
    rcases yz with ⟨y, z⟩
    by_cases hzK : z ∈ K
    · rw [show F (y, z) = ker t y z * g z from rfl, norm_mul, Real.norm_eq_abs (g z)]
      exact mul_le_mul_of_nonneg_right
        ((hC ⟨(y, z), ⟨subset_closure hy, hzK⟩, rfl⟩).trans (le_max_left _ _)) (abs_nonneg _)
    · simp only [F, hz hzK, mul_zero, norm_zero, abs_zero, le_refl]
  have hFi : Integrable F ((μ.restrict A).prod μ) := hDom.mono' hFm hbound
  have hswap := integral_integral_swap (f := fun y z => ker t y z * g z) hFi
  calc
    _ = (μ.real A)⁻¹ * ∫ z, ∫ y in A, ker t y z * g z ∂μ ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp only [kernelAverage]
        rw [integral_mul_const]
        ring
    _ = _ := congrArg (fun q : ℝ => (μ.real A)⁻¹ * q) hswap.symm

end RegularPointCoordinates

end

end OAI
