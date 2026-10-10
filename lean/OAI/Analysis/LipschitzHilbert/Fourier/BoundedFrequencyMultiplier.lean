import OAI.Analysis.LipschitzHilbert.Fourier.FiniteBandMultiplier

namespace OAI

/-! A bounded measurable frequency symbol can be paired with an L1 test
function. This justifies finite recombination before the uniform estimates. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def variableFrequencyMultiplier (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) : ℂ :=
  ∫ omega, Real.fourierChar (z.1*omega.1+z.2*omega.2) •
    (m (z,omega)*planarFourier f omega) ∂planeMeasure

theorem variableFrequencyMultiplier_measurable (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ)
    (hm : Measurable m) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    Measurable (variableFrequencyMultiplier m f) := by
  have hp : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) =>
      (Real.fourierChar (p.1.1*p.2.1+p.1.2*p.2.2):ℂ)) := by fun_prop
  have hF : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) => planarFourier f p.2) := by
    have heq : (planarFourierSchwartz f : ℝ×ℝ → ℂ)=planarFourier f :=
      funext (planarFourierSchwartz_apply f)
    exact (heq ▸ (planarFourierSchwartz f).continuous.measurable).comp measurable_snd
  exact ((hp.mul (hm.mul hF)).stronglyMeasurable.integral_prod_right').measurable

theorem variableFrequencyMultiplier_bound (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ)
    (C : ℝ) (hbound : ∀ z omega, ‖m (z,omega)‖≤C)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    ‖variableFrequencyMultiplier m f z‖≤C*∫ omega, ‖planarFourier f omega‖ ∂planeMeasure := by
  have h := norm_integral_le_of_norm_le ((planarFourier_integrable f).norm.const_mul C)
    (Filter.Eventually.of_forall (fun omega => show
      ‖Real.fourierChar (z.1*omega.1+z.2*omega.2) • (m (z,omega)*planarFourier f omega)‖≤
      C*‖planarFourier f omega‖ from by
        rw [Circle.norm_smul,norm_mul]
        exact mul_le_mul_of_nonneg_right (hbound z omega) (norm_nonneg _)))
  simpa only [variableFrequencyMultiplier,planeMeasure,integral_const_mul] using h

theorem variableFrequencyMultiplier_pairing_integrable (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ)
    (hm : Measurable m) (C : ℝ) (hbound : ∀ z omega, ‖m (z,omega)‖≤C)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (g : ℝ×ℝ → ℂ) (hg : Integrable g planeMeasure) :
    Integrable (fun z => variableFrequencyMultiplier m f z*star (g z)) planeMeasure := by
  have hmeas := (variableFrequencyMultiplier_measurable m hm f).aestronglyMeasurable (μ:=planeMeasure)
  apply (hg.norm.const_mul (C*∫ omega, ‖planarFourier f omega‖ ∂planeMeasure)).mono'
    (hmeas.mul hg.aestronglyMeasurable.star)
  filter_upwards [] with z
  change ‖variableFrequencyMultiplier m f z*star (g z)‖≤_
  rw [norm_mul,norm_star]
  exact mul_le_mul_of_nonneg_right (variableFrequencyMultiplier_bound m C hbound f z) (norm_nonneg _)

end LipschitzHilbert.PacketRepresentation

end

end OAI
