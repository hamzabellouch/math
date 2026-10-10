import Mathlib
import OAI.Probability.Ballisticity.Entropy.EntropyPlus

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace DirectionalTransience.Entropy

lemma density_of_finite_kl {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hkl : klDiv μ ν≠∞) :
    ∃ g : X → ℝ, Measurable g ∧ (∀ x, 0≤g x) ∧ Integrable g ν ∧
      (∫ x, g x ∂ν)=1 ∧ Integrable (fun x => TailDecorrelation.entropyPlus (g x)) ν ∧
      μ=ν.withDensity (fun x => ENNReal.ofReal (g x)) := by
  obtain ⟨hac,hint⟩ := klDiv_ne_top_iff.mp hkl
  let g : X → ℝ := fun x => (μ.rnDeriv ν x).toReal
  have hg : Measurable g := (Measure.measurable_rnDeriv μ ν).ennreal_toReal
  have hgi : Integrable g ν := by
    simpa only [mul_one] using
      (integrable_toReal_rnDeriv_mul_iff hac (f := fun _ => (1:ℝ))).mpr (integrable_const 1)
  have hg1 : (∫ x, g x ∂ν)=1 := by
    simpa only [mul_one,integral_const,probReal_univ,one_smul] using
      (integral_toReal_rnDeriv_mul hac (f := fun _ => (1:ℝ)))
  have hpos : Integrable (fun x => Real.log (max 1 (g x))) μ := by
    apply hint.abs.mono' (measurable_const.max hg).log.aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (le_max_left _ _))]
    change Real.log (max 1 (g x))≤|Real.log (g x)|
    by_cases h : g x≤1
    · simp only [max_eq_left h,Real.log_one,abs_nonneg]
    · rw [max_eq_right (le_of_not_ge h)]
      exact le_abs_self _
  have hH := (integrable_toReal_rnDeriv_mul_iff hac).mpr hpos
  refine ⟨g,hg,fun _ => ENNReal.toReal_nonneg,hgi,hg1,hH,?_⟩
  rw [←Measure.withDensity_rnDeriv_eq μ ν hac]
  apply withDensity_congr_ae
  filter_upwards [Measure.rnDeriv_ne_top μ ν] with x hx
  exact (ENNReal.ofReal_toReal hx).symm

end DirectionalTransience.Entropy

end

end OAI
