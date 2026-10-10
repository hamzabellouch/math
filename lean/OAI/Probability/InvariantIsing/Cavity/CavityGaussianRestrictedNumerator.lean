import OAI.Probability.InvariantIsing.Cavity.CavityLabeledRestrictedNumerator

namespace OAI

/-! The Gaussian-first hard-restricted formula is the ordinary replica numerator
of the full labeled cavity prior, with one residual sampled per replica. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_gaussian_restricted_numerator {m n r d k : ℕ}
    (T : LabeledTree n) (ν : Measure (LabeledLeaf n)) [IsProbabilityMeasure ν]
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ Bcut : ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    (∫ z, ∫ α, cavityRestrictedFlatSpinValue K L C τ Bcut π (fun ε => F (B α, ε))
        (cavityReplicaField n T α z) ∂Measure.pi (fun _ : Fin r => ν)
      ∂(((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
        (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
          (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))).prod
            (Measure.pi (fun _ : Fin r => multivariateGaussian
              (0 : EuclideanSpace ℝ (Fin d)) R)))) =
      ∫ sg, cavityWeightNumerator ((ν.prod (multivariateGaussian 0 R)).prod π)
        (fun p => cavityRestrictedFactor K L C τ Bcut
          (cavityLeafSum n sg.1
            (labeledNoiseLeaf _ n (T, markForestOfCoords _ n sg.2) p.1.1) + p.1.2) p.2)
        (fun ξ => F (B (fun i => (ξ i).1.1), fun i => (ξ i).2))
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
          (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v)))) := by
  let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
    (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))
  let μ := Measure.pi (fun _ : Fin r => multivariateGaussian
    (0 : EuclideanSpace ℝ (Fin d)) R)
  let V := fun z : (EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) ×
      (Fin r → EuclideanSpace ℝ (Fin d)) =>
    ∫ α, cavityRestrictedFlatSpinValue K L C τ Bcut π (fun ε => F (B α, ε))
      (cavityReplicaField n T α z) ∂Measure.pi (fun _ : Fin r => ν)
  have hm : Measurable (fun zα :
      ((EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) ×
        (Fin r → EuclideanSpace ℝ (Fin d))) × (Fin r → LabeledLeaf n) =>
      cavityRestrictedFlatSpinValue K L C τ Bcut π (fun ε => F (B zα.2, ε))
        (cavityReplicaField n T zα.2 zα.1)) := by
    apply measurable_from_prod_countable_left
    intro α
    exact (measurable_cavityRestrictedFlatSpinValue K L C τ Bcut π (fun ε => F (B α, ε))).comp
      (measurable_cavityReplicaField n T α)
  have hV : Measurable V := hm.stronglyMeasurable.integral_prod_right'.measurable
  have hb (z) : ‖V z‖ ≤ (Real.exp τ)^r * ‖F‖ := by
    have hh := norm_integral_le_of_norm_le_const
      (μ := Measure.pi (fun _ : Fin r => ν)) (ae_of_all _ fun α =>
        cavityRestrictedFlatSpinValue_bound K L C τ Bcut π (fun ε => F (B α, ε))
          (fun ε => F.norm_coe_le_norm (B α, ε)) (cavityReplicaField n T α z))
    simpa only [V, probReal_univ, mul_one] using hh
  have hi : Integrable V (P.prod μ) :=
    (integrable_const ((Real.exp τ)^r * ‖F‖)).mono' hV.aestronglyMeasurable (ae_of_all _ hb)
  change (∫ z, V z ∂P.prod μ) = _
  rw [integral_prod V hi]
  apply integral_congr_ae
  exact ae_of_all _ fun sg =>
    (cavity_labeled_restricted_numerator ν R K L C τ Bcut π
      (fun α => cavityLeafSum n sg.1 (labeledNoiseLeaf _ n
        (T, markForestOfCoords _ n sg.2) α)) B F).symm

end InvariantIsing

end

end OAI
