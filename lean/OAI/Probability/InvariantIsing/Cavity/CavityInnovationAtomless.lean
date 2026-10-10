import OAI.Probability.InvariantIsing.Cavity.CavityGaussianMarkDepth

namespace OAI

/-! Atomlessness passes through the actual weighted affine Gaussian innovation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix MatrixOrder

namespace InvariantIsing

lemma cavity_nullSingleton_map {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [NullSingletonClass μ]
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : Measurable f) (hi : Function.Injective f) : NullSingletonClass (μ.map f) := by
  constructor
  intro x
  rw [Measure.map_apply hf (measurableSet_singleton x)]
  by_cases h : ∃ y, f y = x
  · obtain ⟨y, rfl⟩ := h
    have hp : f ⁻¹' {f y} = {y} := by
      ext z
      exact hi.eq_iff
    rw [hp, measure_singleton]
  · have hp : f ⁻¹' {x} = ∅ := by
      ext y
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      exact fun hy => h ⟨y, hy⟩
    rw [hp, measure_empty]

lemma cavity_quadratic_innovation_nullSingleton {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ)
    (hK : K.transpose = K) (hC : C.transpose = C) (hS : S.PosSemidef)
    (ζ : ℝ) (hζ : 0 < ζ)
    (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S)
    (hQ : (cavityFactorPrecision (ζ • cavityBackwardQuadratic K C) (CFC.sqrt S)).PosDef)
    [NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S)] :
    NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
      ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose)) := by
  let μ := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S).withDensity
    (fun a => ENNReal.ofReal (cavityQuadraticStepWeight K P C ζ (0, a) ^ ζ))
  let f := fun a : EuclideanSpace ℝ (Fin d) => cavityStepInnovation K P C (0, a)
  have hm : Measurable f :=
    (measurable_cavityStepInnovation K P C).comp (measurable_const.prodMk measurable_id)
  have hi : Function.Injective f := cavityStepInnovation_injective K P C hCdet 0
  have ha : NullSingletonClass (μ.map f) := cavity_nullSingleton_map μ f hm hi
  have he : μ.map f = multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
      ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose) :=
    cavity_quadratic_step_weight_innovation_law K P C S hK hC hS ζ hζ hPdet hCdet hΔ hQ 0
  exact he ▸ ha

end InvariantIsing

end

end OAI
