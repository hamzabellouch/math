import OAI.Analysis.LipschitzHilbert.Fourier.BoundedFrequencyMultiplier
import OAI.Analysis.LipschitzHilbert.Fourier.L1FourierConvolution

namespace OAI

/-! Integrable frequency envelopes justify multipliers and finite
recombination for L1 inputs, including discontinuous amplitude slices. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

def variableFrequencyMultiplierL1 (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ)
    (f : ℝ×ℝ → ℂ) (z : ℝ×ℝ) : ℂ :=
  ∫ omega, Real.fourierChar (z.1*omega.1+z.2*omega.2) •
    (m (z,omega)*planarFourier f omega) ∂planeMeasure

theorem variableFrequencyMultiplier_measurable_l1
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (hm : Measurable m)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) :
    Measurable (variableFrequencyMultiplierL1 m f) := by
  have hp : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) =>
      (Real.fourierChar (p.1.1*p.2.1+p.1.2*p.2.2):ℂ)) := by fun_prop
  have hF : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) => planarFourier f p.2) :=
    (planarFourier_l1_continuous f hf).measurable.comp measurable_snd
  exact ((hp.mul (hm.mul hF)).stronglyMeasurable.integral_prod_right').measurable

theorem variableFrequencyMultiplier_integrand_integrable_l1
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (hm : Measurable m)
    (q : ℝ×ℝ → ℝ) (hq : Integrable q planeMeasure)
    (hbound : ∀ z omega, ‖m (z,omega)‖≤q omega)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) (z : ℝ×ℝ) :
    Integrable (fun omega => Real.fourierChar (z.1*omega.1+z.2*omega.2) •
      (m (z,omega)*planarFourier f omega)) planeMeasure := by
  have hp : Measurable (fun omega : ℝ×ℝ =>
      (Real.fourierChar (z.1*omega.1+z.2*omega.2):ℂ)) := by fun_prop
  have hm' : Measurable (fun omega => m (z,omega)) :=
    hm.comp (measurable_const.prodMk measurable_id)
  apply (hq.mul_const (∫ x, ‖f x‖ ∂planeMeasure)).mono'
    (hp.mul (hm'.mul (planarFourier_l1_continuous f hf).measurable)).aestronglyMeasurable
  filter_upwards [] with omega
  change ‖(Real.fourierChar (z.1*omega.1+z.2*omega.2):ℂ)*
    (m (z,omega)*planarFourier f omega)‖≤_
  rw [norm_mul,Circle.norm_coe,one_mul,norm_mul]
  exact mul_le_mul (hbound z omega) (planarFourier_l1_bound f omega)
    (norm_nonneg _) ((norm_nonneg _).trans (hbound z omega))

theorem variableFrequencyMultiplier_bound_l1
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ)
    (q : ℝ×ℝ → ℝ) (hq : Integrable q planeMeasure)
    (hbound : ∀ z omega, ‖m (z,omega)‖≤q omega)
    (f : ℝ×ℝ → ℂ) (z : ℝ×ℝ) :
    ‖variableFrequencyMultiplierL1 m f z‖≤
      (∫ omega, q omega ∂planeMeasure)*(∫ x, ‖f x‖ ∂planeMeasure) := by
  have h := norm_integral_le_of_norm_le (hq.mul_const (∫ x, ‖f x‖ ∂planeMeasure))
    (Filter.Eventually.of_forall (fun omega => show
      ‖Real.fourierChar (z.1*omega.1+z.2*omega.2) • (m (z,omega)*planarFourier f omega)‖≤
        q omega*(∫ x, ‖f x‖ ∂planeMeasure) from by
      rw [Circle.norm_smul,norm_mul]
      exact mul_le_mul (hbound z omega) (planarFourier_l1_bound f omega)
        (norm_nonneg _) ((norm_nonneg _).trans (hbound z omega))))
  simpa only [variableFrequencyMultiplierL1,planeMeasure,integral_mul_const] using h

theorem variableFrequencyMultiplier_pairing_integrable_l1
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (hm : Measurable m)
    (q : ℝ×ℝ → ℝ) (hq : Integrable q planeMeasure)
    (hbound : ∀ z omega, ‖m (z,omega)‖≤q omega)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure)
    (g : ℝ×ℝ → ℂ) (hg : Integrable g planeMeasure) :
    Integrable (fun z => variableFrequencyMultiplierL1 m f z*star (g z)) planeMeasure := by
  have hmeas := (variableFrequencyMultiplier_measurable_l1 m hm f hf).aestronglyMeasurable (μ:=planeMeasure)
  apply (hg.norm.const_mul ((∫ omega, q omega ∂planeMeasure)*(∫ x, ‖f x‖ ∂planeMeasure))).mono'
    (hmeas.mul hg.aestronglyMeasurable.star)
  filter_upwards [] with z
  change ‖variableFrequencyMultiplierL1 m f z*star (g z)‖≤_
  rw [norm_mul,norm_star]
  exact mul_le_mul_of_nonneg_right (variableFrequencyMultiplier_bound_l1 m q hq hbound f z) (norm_nonneg _)

theorem finite_variableFrequencyMultiplier_pairing_l1 {ι : Type*} [Fintype ι]
    (m : ι → (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (hm : ∀ i, Measurable (m i))
    (q : ι → ℝ×ℝ → ℝ) (hq : ∀ i, Integrable (q i) planeMeasure)
    (hbound : ∀ i z omega, ‖m i (z,omega)‖≤q i omega)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure)
    (g : ℝ×ℝ → ℂ) (hg : Integrable g planeMeasure) :
    (∑ i, ∫ z, variableFrequencyMultiplierL1 (m i) f z*star (g z) ∂planeMeasure)=
      ∫ z, variableFrequencyMultiplierL1 (fun p => ∑ i, m i p) f z*star (g z) ∂planeMeasure := by
  classical
  rw [←integral_finsetSum _ (fun i _ =>
    variableFrequencyMultiplier_pairing_integrable_l1 (m i) (hm i) (q i) (hq i) (hbound i) f hf g hg)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [←Finset.sum_mul]
  congr 1
  unfold variableFrequencyMultiplierL1
  rw [←integral_finsetSum _ (fun i _ =>
    variableFrequencyMultiplier_integrand_integrable_l1 (m i) (hm i) (q i) (hq i) (hbound i) f hf z)]
  apply integral_congr_ae
  filter_upwards [] with omega
  simp only [Finset.sum_mul,Finset.smul_sum]

end LipschitzHilbert.PacketRepresentation

end

end OAI
