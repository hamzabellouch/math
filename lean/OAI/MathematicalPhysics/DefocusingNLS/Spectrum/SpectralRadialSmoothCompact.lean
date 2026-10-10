import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialDominatingWeight

namespace OAI

/-! Weakly null bounded smooth radial jets converge strongly in volume L². -/

open Set MeasureTheory Filter Topology
open scoped SchwartzMap
namespace DefocusingNLS

theorem radialPressureMeasure_ae_positive (R : ℝ) :
    ∀ᵐ r ∂radialPressureMeasure R, 0 < r ∧ r ≤ R := by
  unfold radialPressureMeasure
  apply (ae_withDensity_iff (by fun_prop)).2
  have hn : ∀ᵐ r : ℝ ∂volume, r ≠ 0 := by
    simp only [ae_iff]
    simp
  filter_upwards [ae_restrict_mem measurableSet_Icc,hn.filter_mono ae_restrict_le] with r hr hne _
  exact ⟨lt_of_le_of_ne hr.1 (Ne.symm hne),hr.2⟩

theorem spectralRadialSmoothValue_norm_sq (R : ℝ) (f : 𝓢(ℝ,ℂ)) :
    ‖spectralRadialSmoothValue R f‖^2=∫ r, ‖f r‖^2 ∂radialPressureMeasure R := by
  rw [← real_inner_self_eq_norm_sq]
  change (∫ r, inner ℝ (spectralRadialSmoothValue R f r) (spectralRadialSmoothValue R f r)
    ∂radialPressureMeasure R)=_
  apply integral_congr_ae
  filter_upwards [spectralRadialSmoothValue_ae R f] with r hr
  rw [hr,real_inner_self_eq_norm_sq]

theorem spectralRadialSmooth_weakNull_volume (R : ℝ) (hR : 0 < R)
    (f : ℕ → 𝓢(ℝ,ℂ)) (M : ℝ)
    (hf : ∀ n, ‖spectralRadialSmoothEmbedding R (f n)‖ ≤ M)
    (hweak : ∀ L : SpectralRadialEnergy R →L[ℂ] ℂ,
      Tendsto (fun n => L (spectralRadialSmoothEmbedding R (f n))) atTop (𝓝 0)) :
    Tendsto (fun n => spectralRadialSmoothValue R (f n)) atTop (𝓝 0) := by
  let B := fun r => spectralRadialEvaluationWeight R hR r*M^2
  have hB : Integrable B (radialPressureMeasure R) :=
    (spectralRadialEvaluationWeight_integrable R hR).mul_const _
  have hbound (n : ℕ) : ∀ᵐ r ∂radialPressureMeasure R, ‖‖f n r‖^2‖ ≤ B r := by
    filter_upwards [radialPressureMeasure_ae_positive R] with r hr
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have hb := spectralRadialSmooth_sq_bound R hR r hr.1 hr.2 (f n)
    apply hb.trans
    have hw : 0 ≤ spectralRadialEvaluationWeight R hR r := by
      unfold spectralRadialEvaluationWeight
      positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hf n) 2) hw
  have hp : ∀ᵐ r ∂radialPressureMeasure R,
      Tendsto (fun n => ‖f n r‖^2) atTop (𝓝 0) := by
    filter_upwards [radialPressureMeasure_ae_positive R] with r hr
    have ht := hweak (spectralRadialPointValue R hR r hr.1)
    simp only [spectralRadialPointValue_smooth R hR r hr.1 hr.2] at ht
    simpa only [norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)] using ht.norm.pow 2
  have hi : Tendsto (fun n => ∫ r, ‖f n r‖^2 ∂radialPressureMeasure R) atTop (𝓝 0) := by
    have hm (n : ℕ) : AEStronglyMeasurable (fun r => ‖f n r‖^2) (radialPressureMeasure R) := by
      fun_prop
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence B
      hm hB hbound hp
  have hs : Tendsto (fun n => ‖spectralRadialSmoothValue R (f n)‖^2) atTop (𝓝 0) := by
    simpa only [spectralRadialSmoothValue_norm_sq] using hi
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hh

end DefocusingNLS

end OAI
