import OAI.Geometry.Perimeter.Regularity.GeoAlgebra

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n m : ℕ}

theorem weighted_square_L1_tendsto_zero {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (f : ℕ → X → ℝ) (hf : ∀ i, Integrable (f i) μ)
    {g w φ : X → ℝ} (hg : Integrable g μ) (hw : AEStronglyMeasurable w μ)
    (hφ : AEStronglyMeasurable φ μ) {M A B : ℝ} (hM : 0≤M) (hA : 0≤A) (hB : 0≤B)
    (hbφ : ∀ᵐ x ∂μ, ‖φ x‖≤M)
    (heq : ∀ᵐ x ∂μ, φ x≠0 → w x=g x)
    (hbw : ∀ᵐ x ∂μ, φ x≠0 → ‖w x‖≤B)
    (hbf : ∀ᶠ i in atTop, ∀ᵐ x ∂μ, φ x≠0 → ‖f i x‖≤A)
    (hL : Tendsto (fun i ↦ ∫⁻ x, ‖f i x-g x‖ₑ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, φ x*(f i x-w x)^2 ∂μ) atTop (𝓝 0) := by
  have hbound : ∀ᶠ i in atTop, ∀ᵐ x ∂μ,
      ‖φ x*(f i x-w x)^2‖≤M*(A+B)*‖f i x-g x‖ := by
    filter_upwards [hbf] with i hi
    filter_upwards [hi,hbw,heq,hbφ] with x hix hwx hex hφx
    by_cases hz : φ x=0
    · simp only [hz,zero_mul,norm_zero]
      positivity
    · have hab : ‖f i x-w x‖≤A+B := (norm_sub_le _ _).trans (add_le_add (hix hz) (hwx hz))
      rw [norm_mul,norm_pow]
      calc
        _ ≤ M*(‖f i x-w x‖*‖f i x-w x‖) := by rw [← pow_two]; gcongr
        _ ≤ M*((A+B)*‖f i x-w x‖) := by gcongr
        _ = _ := by rw [hex hz]; ring
  have hi : ∀ᶠ i in atTop, Integrable (fun x ↦ φ x*(f i x-w x)^2) μ := by
    filter_upwards [hbound] with i hib
    exact (((hf i).sub hg).norm.const_mul (M*(A+B))).mono'
      (hφ.mul (((hf i).aestronglyMeasurable.sub hw).pow 2)) hib
  have ht : Tendsto (fun i ↦ ENNReal.ofReal (M*(A+B)) * ∫⁻ x, ‖f i x-g x‖ₑ ∂μ)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hL (Or.inr ENNReal.ofReal_ne_top)
  have hl : Tendsto (fun i ↦ ∫⁻ x, ‖φ x*(f i x-w x)^2‖ₑ ∂μ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
      (Eventually.of_forall (fun _ ↦ zero_le)) ?_
    filter_upwards [hbound] with i hib
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [hib] with x hx
    rw [← ofReal_norm,← ofReal_norm,← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hx
  have h := tendsto_integral_of_L1 (fun _ : X ↦ (0:ℝ))
    (aestronglyMeasurable_zero : AEStronglyMeasurable (fun _ : X ↦ (0:ℝ)) μ) hi
    (by simpa only [sub_zero] using hl)
  simpa only [integral_zero] using h

end RPISingularHarnack

end

end OAI
