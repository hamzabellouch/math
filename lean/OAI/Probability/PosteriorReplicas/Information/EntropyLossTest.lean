import OAI.Probability.PosteriorReplicas.Information.EntropyTest

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma entropy_loss_test {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hkl : klDiv μ ν ≠ ∞) {ψ : X → Y} (hψ : Measurable ψ)
    {g : Y → ℝ} (hg : Measurable g)
    (he : Integrable (fun y => Real.exp (g y)) (ν.map ψ))
    (hmean : (∫ y, Real.exp (g y) ∂ν.map ψ) ≤ 1)
    (herr : Integrable (fun x => max (llr μ ν x - g (ψ x)) 0) μ) :
    Integrable (fun x => g (ψ x)) μ ∧
      Integrable (fun x => llr μ ν x - g (ψ x)) μ ∧
      (klDiv μ ν).toReal ≤ (klDiv (μ.map ψ) (ν.map ψ)).toReal +
        ∫ x, llr μ ν x - g (ψ x) ∂μ := by
  have hkl' : klDiv (μ.map ψ) (ν.map ψ) ≠ ∞ := ne_top_of_le_ne_top hkl (klDiv_map_le μ ν hψ)
  obtain ⟨hac,hllr⟩ := klDiv_ne_top_iff.mp hkl
  have hp := (entropy_test_positive_integrable (μ.map ψ) (ν.map ψ) hkl' hg he).comp_measurable hψ
  have hb := (hllr.norm.add hp).add herr
  have hgi : Integrable (fun x => g (ψ x)) μ := by
    apply hb.mono' (hg.comp hψ).aestronglyMeasurable
    apply ae_of_all
    intro x
    simp only [Pi.add_apply, Function.comp_def, Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · have h₁ := neg_abs_le (llr μ ν x)
      have h₂ := le_max_left (llr μ ν x-g (ψ x)) 0
      have h₃ := le_max_right (g (ψ x)) 0
      linarith
    · have h₁ := le_max_left (g (ψ x)) 0
      have h₂ := abs_nonneg (llr μ ν x)
      have h₃ := le_max_right (llr μ ν x-g (ψ x)) 0
      linarith
  refine ⟨hgi,hllr.sub hgi,?_⟩
  have hgm : Integrable g (μ.map ψ) := (integrable_map_measure hg.aestronglyMeasurable hψ.aemeasurable).mpr hgi
  have ht := entropy_test_normalized (μ.map ψ) (ν.map ψ) hkl' hgm he hmean
  rw [integral_map hψ.aemeasurable hg.aestronglyMeasurable] at ht
  rw [toReal_klDiv_of_measure_eq hac (by simp), integral_sub hllr hgi]
  linarith

end PosteriorReplicas
end

end OAI
