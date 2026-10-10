import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialIntervalKernel

namespace OAI

/-! Local derivative energy controls radial increments across the cutoff collar. -/

open Set MeasureTheory
namespace DefocusingNLS

private theorem intervalMask_measurable (l r : ℝ) :
    Measurable ((Icc l r).indicator (fun _ : ℝ => (1 : ℝ))) :=
  measurable_const.indicator measurableSet_Icc

private theorem intervalMask_bound (R l r : ℝ) :
    ∀ᵐ s ∂radialPressureMeasure R, ‖(Icc l r).indicator (fun _ : ℝ => (1 : ℝ)) s‖ ≤ 1 := by
  apply Filter.Eventually.of_forall
  intro s
  by_cases hs : s ∈ Icc l r <;> simp [hs]

noncomputable def spectralRadialIntervalMask (R l r : ℝ) :
    SpectralRadialL2 R →L[ℝ] SpectralRadialL2 R :=
  spectralPressureOperator R ((Icc l r).indicator (fun _ : ℝ => (1 : ℝ)))
    (intervalMask_measurable l r).aestronglyMeasurable (intervalMask_bound R l r)

theorem spectralRadialIntervalMask_ae (R l r : ℝ) (u : SpectralRadialL2 R) :
    spectralRadialIntervalMask R l r u =ᵐ[radialPressureMeasure R]
      fun s => (Icc l r).indicator (fun _ : ℝ => (1 : ℝ)) s • u s :=
  spectralPressureProduct_ae R ((Icc l r).indicator (fun _ : ℝ => (1 : ℝ)))
    (intervalMask_measurable l r).aestronglyMeasurable (intervalMask_bound R l r) u

theorem spectralRadialIntervalMask_norm_sq (R l r : ℝ) (u : SpectralRadialL2 R) :
    ‖spectralRadialIntervalMask R l r u‖^2=
      ∫ s in Icc l r, ‖u s‖^2 ∂radialPressureMeasure R := by
  rw [← real_inner_self_eq_norm_sq]
  change (∫ s, inner ℝ (spectralRadialIntervalMask R l r u s)
    (spectralRadialIntervalMask R l r u s) ∂radialPressureMeasure R)=_
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [spectralRadialIntervalMask_ae R l r u] with s hs
  rw [hs,real_inner_self_eq_norm_sq]
  by_cases hm : s ∈ Icc l r <;> simp [hm]

theorem spectralRadialIntervalKernel_inner_local (R l r U : ℝ) (hl : 0 < l)
    (hrU : r ≤ U) (u : SpectralRadialL2 R) :
    inner ℂ (spectralRadialIntervalKernel R l r hl) u=
      inner ℂ (spectralRadialIntervalKernel R l r hl) (spectralRadialIntervalMask R l U u) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [spectralRadialIntervalKernel_ae R l r hl,
    spectralRadialIntervalMask_ae R l U u] with s hk hu
  rw [hk,hu]
  by_cases hs : s ∈ Icc l r
  · have hsU : s ∈ Icc l U := ⟨hs.1,hs.2.trans hrU⟩
    simp only [indicator_of_mem hsU,one_smul]
  · simp [spectralPrimitiveKernelValue,hs]

theorem spectralRadialPointValue_local_increment (R l r U : ℝ) (hR : 0 < R)
    (hl : 0 < l) (hlr : l ≤ r) (hrU : r ≤ U) (hUR : U ≤ R) (u : SpectralRadialEnergy R) :
    ‖spectralRadialPointValue R hR r (hl.trans_le hlr) u-spectralRadialPointValue R hR l hl u‖^2 ≤
      (r-l)*(l^11)⁻¹*‖spectralRadialIntervalMask R l U (spectralRadialDerivative R u)‖^2 := by
  rw [spectralRadialPointValue_increment R l r hR hl hlr (hrU.trans hUR),
    spectralRadialIntervalKernel_inner_local R l r U hl hrU]
  have hi := norm_inner_le_norm (𝕜 := ℂ) (spectralRadialIntervalKernel R l r hl)
    (spectralRadialIntervalMask R l U (spectralRadialDerivative R u))
  calc
    _ ≤ (‖spectralRadialIntervalKernel R l r hl‖*
        ‖spectralRadialIntervalMask R l U (spectralRadialDerivative R u)‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hi 2
    _ = ‖spectralRadialIntervalKernel R l r hl‖^2*
        ‖spectralRadialIntervalMask R l U (spectralRadialDerivative R u)‖^2 := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (spectralRadialIntervalKernel_bound R l r hl hlr (hrU.trans hUR)) (sq_nonneg _)

end DefocusingNLS

end OAI
