import OAI.Analysis.LipschitzHilbert.Fourier.L1FrequencyMultiplier

namespace OAI

/-! Dominated convergence for the exact L1 frequency multiplier pairing.
The frequency envelope is fixed for a given finite band. -/
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform Topology
namespace LipschitzHilbert.PacketRepresentation

theorem planarFourier_tendsto_dominated
    (f : ℝ×ℝ → ℂ) (fseq : ℕ → (ℝ×ℝ) → ℂ) (hf : Integrable f planeMeasure)
    (hseq : ∀ n, Integrable (fseq n) planeMeasure)
    (hbound : ∀ n, ∀ᵐ x ∂planeMeasure, ‖fseq n x‖≤‖f x‖)
    (hlim : ∀ᵐ x ∂planeMeasure, Tendsto (fun n => fseq n x) atTop (𝓝 (f x)))
    (omega : ℝ×ℝ) :
    Tendsto (fun n => planarFourier (fseq n) omega) atTop (𝓝 (planarFourier f omega)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
  · intro n
    exact (show Continuous (fun x : ℝ×ℝ => Real.fourierChar (-(x.1*omega.1+x.2*omega.2))) by
      fun_prop).aestronglyMeasurable.smul (hseq n).aestronglyMeasurable
  · exact hf.norm
  · intro n
    filter_upwards [hbound n] with x hx
    rwa [Circle.norm_smul]
  · filter_upwards [hlim] with x hx
    exact tendsto_const_nhds.smul hx

theorem variableFrequencyMultiplier_tendsto_dominated
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (hm : Measurable m)
    (q : ℝ×ℝ → ℝ) (hq : Integrable q planeMeasure)
    (hmb : ∀ z omega, ‖m (z,omega)‖≤q omega)
    (f : ℝ×ℝ → ℂ) (fseq : ℕ → (ℝ×ℝ) → ℂ) (hf : Integrable f planeMeasure)
    (hseq : ∀ n, Integrable (fseq n) planeMeasure)
    (hbound : ∀ n, ∀ᵐ x ∂planeMeasure, ‖fseq n x‖≤‖f x‖)
    (hlim : ∀ᵐ x ∂planeMeasure, Tendsto (fun n => fseq n x) atTop (𝓝 (f x)))
    (z : ℝ×ℝ) :
    Tendsto (fun n => variableFrequencyMultiplierL1 m (fseq n) z) atTop
      (𝓝 (variableFrequencyMultiplierL1 m f z)) := by
  have hmass (n : ℕ) : (∫ x, ‖fseq n x‖ ∂planeMeasure)≤∫ x, ‖f x‖ ∂planeMeasure :=
    integral_mono_ae (hseq n).norm hf.norm (hbound n)
  have hmz : Measurable (fun omega => m (z,omega)) :=
    hm.comp (measurable_const.prodMk measurable_id)
  have hp : Continuous (fun omega : ℝ×ℝ => Real.fourierChar (z.1*omega.1+z.2*omega.2)) := by fun_prop
  apply tendsto_integral_of_dominated_convergence (fun omega => q omega*(∫ x, ‖f x‖ ∂planeMeasure))
  · intro n
    exact hp.aestronglyMeasurable.smul
      (hmz.aestronglyMeasurable.mul (planarFourier_l1_continuous _ (hseq n)).aestronglyMeasurable)
  · exact hq.mul_const _
  · intro n
    filter_upwards [] with omega
    rw [Circle.norm_smul,norm_mul]
    exact mul_le_mul (hmb z omega) ((planarFourier_l1_bound (fseq n) omega).trans (hmass n))
      (norm_nonneg _) ((norm_nonneg _).trans (hmb z omega))
  · filter_upwards [] with omega
    exact tendsto_const_nhds.smul
      (tendsto_const_nhds.mul (planarFourier_tendsto_dominated f fseq hf hseq hbound hlim omega))

theorem variableFrequencyMultiplier_pairing_tendsto_dominated
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (hm : Measurable m)
    (q : ℝ×ℝ → ℝ) (hq : Integrable q planeMeasure)
    (hmb : ∀ z omega, ‖m (z,omega)‖≤q omega)
    (f g : ℝ×ℝ → ℂ) (fseq gseq : ℕ → (ℝ×ℝ) → ℂ)
    (hf : Integrable f planeMeasure) (hg : Integrable g planeMeasure)
    (hfs : ∀ n, Integrable (fseq n) planeMeasure) (hgs : ∀ n, Integrable (gseq n) planeMeasure)
    (hfb : ∀ n, ∀ᵐ x ∂planeMeasure, ‖fseq n x‖≤‖f x‖)
    (hgb : ∀ n, ∀ᵐ x ∂planeMeasure, ‖gseq n x‖≤‖g x‖)
    (hflim : ∀ᵐ x ∂planeMeasure, Tendsto (fun n => fseq n x) atTop (𝓝 (f x)))
    (hglim : ∀ᵐ x ∂planeMeasure, Tendsto (fun n => gseq n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫ z, variableFrequencyMultiplierL1 m (fseq n) z*star (gseq n z) ∂planeMeasure)
      atTop (𝓝 (∫ z, variableFrequencyMultiplierL1 m f z*star (g z) ∂planeMeasure)) := by
  have hqpos : 0≤∫ omega, q omega ∂planeMeasure :=
    integral_nonneg (fun omega => (norm_nonneg (m (0,omega))).trans (hmb 0 omega))
  have hmass (n : ℕ) : (∫ x, ‖fseq n x‖ ∂planeMeasure)≤∫ x, ‖f x‖ ∂planeMeasure :=
    integral_mono_ae (hfs n).norm hf.norm (hfb n)
  have hvbound (n : ℕ) (z : ℝ×ℝ) : ‖variableFrequencyMultiplierL1 m (fseq n) z‖≤
      (∫ omega, q omega ∂planeMeasure)*(∫ x, ‖f x‖ ∂planeMeasure) :=
    (variableFrequencyMultiplier_bound_l1 m q hq hmb (fseq n) z).trans
      (mul_le_mul_of_nonneg_left (hmass n) hqpos)
  apply tendsto_integral_of_dominated_convergence
    (fun z => ((∫ omega, q omega ∂planeMeasure)*(∫ x, ‖f x‖ ∂planeMeasure))*‖g z‖)
  · intro n
    exact (variableFrequencyMultiplier_measurable_l1 m hm (fseq n) (hfs n)).aestronglyMeasurable.mul
      (hgs n).aestronglyMeasurable.star
  · exact hg.norm.const_mul _
  · intro n
    filter_upwards [hgb n] with z hz
    rw [norm_mul,norm_star]
    exact mul_le_mul (hvbound n z) hz (norm_nonneg _) (mul_nonneg hqpos (integral_nonneg (fun _ => norm_nonneg _)))
  · filter_upwards [hglim] with z hz
    exact (variableFrequencyMultiplier_tendsto_dominated m hm q hq hmb f fseq hf hfs hfb hflim z).mul hz.star

end LipschitzHilbert.PacketRepresentation

end

end OAI
