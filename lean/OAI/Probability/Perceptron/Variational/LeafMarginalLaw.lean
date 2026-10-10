import Mathlib
import OAI.Probability.Perceptron.Variational.LeafGibbsMarginal

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SphericalPerceptronFreeEnergy
variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

lemma tiltLaw_prod_snd_of_partition (μ : Measure S) (ν : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : S×T→ℝ) (G : T→ℝ) (hH : Measurable H) (hG : Measurable G)
    (he : Integrable (fun x => Real.exp (H x)) (μ.prod ν))
    (hp : ∀ t, (∫ s, Real.exp (H (s,t)) ∂μ)=Real.exp (G t)) :
    (tiltLaw (μ.prod ν) H 1).map Prod.snd=tiltLaw ν G 1 := by
  have heG : Integrable (fun t => Real.exp (G t)) ν := by
    have hi := he.integral_prod_right
    simpa only [hp] using hi
  have hhe : Integrable (fun x => Real.exp (1*H x)) (μ.prod ν) := by simpa using he
  have hhG : Integrable (fun t => Real.exp (1*G t)) ν := by simpa using heG
  let := tilt_law_probability_of_integrable (μ.prod ν) hhe
  let := tilt_law_probability_of_integrable ν hhG
  apply Measure.ext
  intro s hs
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have hi : Measurable (s.indicator (fun _ : T => (1:ℝ))) := measurable_const.indicator hs
  have hb (t : T) : |s.indicator (fun _ : T => (1:ℝ)) t|≤1 := by
    by_cases ht : t∈s <;> simp [ht]
  have h := tiltMean_prod_snd_of_partition μ ν H G _ hi hb he hp
  rw [←tilt_law_integral_of_integrable (μ.prod ν) hH hhe,
    ←tilt_law_integral_of_integrable ν hG hhG] at h
  have hm := integral_map (μ:=tiltLaw (μ.prod ν) H 1) measurable_snd.aemeasurable hi.aestronglyMeasurable
  rw [←hm] at h
  simpa only [integral_indicator hs,integral_const,smul_eq_mul,mul_one,
    measureReal_def,Measure.restrict_apply_univ] using h

lemma tiltLaw_prod_snd_replica (μ : Measure S) (ν : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : S×T→ℝ) (G : T→ℝ) (hH : Measurable H) (hG : Measurable G)
    (he : Integrable (fun x => Real.exp (H x)) (μ.prod ν))
    (hp : ∀ t, (∫ s, Real.exp (H (s,t)) ∂μ)=Real.exp (G t)) (r : ℕ) :
    MeasurePreserving (fun x : Fin r→S×T => fun i => (x i).2)
      (Measure.pi fun _ : Fin r => tiltLaw (μ.prod ν) H 1)
      (Measure.pi fun _ : Fin r => tiltLaw ν G 1) := by
  have hhe : Integrable (fun x => Real.exp (1*H x)) (μ.prod ν) := by simpa using he
  let := tilt_law_probability_of_integrable (μ.prod ν) hhe
  have heG : Integrable (fun t => Real.exp (1*G t)) ν := by
    simpa only [one_mul,hp] using he.integral_prod_right
  let := tilt_law_probability_of_integrable ν heG
  exact measurePreserving_pi _ _ (fun _ : Fin r =>
    ⟨measurable_snd,tiltLaw_prod_snd_of_partition μ ν H G hH hG he hp⟩)

end SphericalPerceptronFreeEnergy
end

end OAI
