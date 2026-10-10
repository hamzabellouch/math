import OAI.Analysis.LipschitzHilbert.Fourier.BoundedFrequencyMultiplier

namespace OAI

/-! Exact finite recombination of bounded measurable frequency symbols,
with both integral interchanges justified by integrability. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem variableFrequencyMultiplier_integrand_integrable (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ)
    (hm : Measurable m) (C : ℝ) (hbound : ∀ z omega, ‖m (z,omega)‖≤C)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    Integrable (fun omega => Real.fourierChar (z.1*omega.1+z.2*omega.2) •
      (m (z,omega)*planarFourier f omega)) planeMeasure := by
  have hp : Measurable (fun omega : ℝ×ℝ =>
      (Real.fourierChar (z.1*omega.1+z.2*omega.2):ℂ)) := by fun_prop
  have hm' : Measurable (fun omega => m (z,omega)) := hm.comp (measurable_const.prodMk measurable_id)
  have hF : Measurable (planarFourier f) := by
    have heq : (planarFourierSchwartz f : ℝ×ℝ → ℂ)=planarFourier f :=
      funext (planarFourierSchwartz_apply f)
    exact heq ▸ (planarFourierSchwartz f).continuous.measurable
  apply ((planarFourier_integrable f).norm.const_mul C).mono' (hp.mul (hm'.mul hF)).aestronglyMeasurable
  filter_upwards [] with omega
  change ‖(Real.fourierChar (z.1*omega.1+z.2*omega.2):ℂ)*(m (z,omega)*planarFourier f omega)‖≤_
  rw [norm_mul,Circle.norm_coe,one_mul,norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound z omega) (norm_nonneg _)

theorem finite_variableFrequencyMultiplier_pairing {ι : Type*} [Fintype ι]
    (m : ι → (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (hm : ∀ i, Measurable (m i))
    (C : ι → ℝ) (hbound : ∀ i z omega, ‖m i (z,omega)‖≤C i)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (g : ℝ×ℝ → ℂ) (hg : Integrable g planeMeasure) :
    (∑ i, ∫ z, variableFrequencyMultiplier (m i) f z*star (g z) ∂planeMeasure)=
      ∫ z, variableFrequencyMultiplier (fun p => ∑ i, m i p) f z*star (g z) ∂planeMeasure := by
  classical
  rw [←integral_finsetSum _ (fun i _ =>
    variableFrequencyMultiplier_pairing_integrable (m i) (hm i) (C i) (hbound i) f g hg)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [←Finset.sum_mul]
  congr 1
  unfold variableFrequencyMultiplier
  rw [←integral_finsetSum _ (fun i _ =>
    variableFrequencyMultiplier_integrand_integrable (m i) (hm i) (C i) (hbound i) f z)]
  apply integral_congr_ae
  filter_upwards [] with omega
  simp only [Finset.sum_mul,Finset.smul_sum]

end LipschitzHilbert.PacketRepresentation

end

end OAI
