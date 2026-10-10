import OAI.Probability.InvariantIsing.Cavity.CavityGaussianKernel

namespace OAI

/-! The joint law of an overlap label and its Gaussian cavity marks.
The covariance is allowed to be singular. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

variable {a L : Type*} [Fintype a] [DecidableEq a]
  [MetricSpace L] [MeasurableSpace L] [BorelSpace L]

def cavityGaussianMarkedMap
    (p : (L × Matrix a a ℝ) × EuclideanSpace ℝ a) : L × EuclideanSpace ℝ a :=
  (p.1.1, p.2)

omit [Fintype a] [DecidableEq a] [MetricSpace L] [BorelSpace L] in
lemma measurable_cavityGaussianMarkedMap :
    Measurable (cavityGaussianMarkedMap (a := a) (L := L)) :=
  measurable_fst.fst.prodMk measurable_snd

def cavityGaussianMarkedLaw (Q : ProbabilityMeasure (L × Matrix a a ℝ)) :
    ProbabilityMeasure (L × EuclideanSpace ℝ a) :=
  ⟨((Q : Measure _).compProd cavityGaussianKernel).map cavityGaussianMarkedMap,
    (Measure.isProbabilityMeasure_map_iff
      measurable_cavityGaussianMarkedMap.aemeasurable).mpr inferInstance⟩

omit [BorelSpace L] in
lemma cavityGaussianMarkedLaw_integral [SecondCountableTopology L]
    (Q : ProbabilityMeasure (L × Matrix a a ℝ))
    (f : L × EuclideanSpace ℝ a → ℝ) (hf : Measurable f)
    {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, f x ∂(cavityGaussianMarkedLaw Q : Measure (L × EuclideanSpace ℝ a))) =
      ∫ p, ∫ y, f (p.1, y) ∂multivariateGaussian 0 p.2
        ∂(Q : Measure (L × Matrix a a ℝ)) := by
  have hi : Integrable (fun p => f (cavityGaussianMarkedMap p))
      ((Q : Measure (L × Matrix a a ℝ)).compProd cavityGaussianKernel) :=
    Integrable.of_bound (hf.comp measurable_cavityGaussianMarkedMap).aestronglyMeasurable
      C (ae_of_all _ fun p => hb _)
  change (∫ x, f x ∂((Q : Measure (L × Matrix a a ℝ)).compProd cavityGaussianKernel).map
    cavityGaussianMarkedMap) = _
  rw [integral_map measurable_cavityGaussianMarkedMap.aemeasurable hf.aestronglyMeasurable,
    Measure.integral_compProd hi]
  rfl

theorem cavityGaussianMarkedLaw_tendsto [SecondCountableTopology L]
    (Q : ℕ → ProbabilityMeasure (L × Matrix a a ℝ))
    (Q₀ : ProbabilityMeasure (L × Matrix a a ℝ))
    (hQ : Tendsto Q atTop (𝓝 Q₀))
    (hS : ∀ n, ∀ᵐ p ∂(Q n : Measure (L × Matrix a a ℝ)), p.2.PosSemidef)
    (hS₀ : ∀ᵐ p ∂(Q₀ : Measure (L × Matrix a a ℝ)), p.2.PosSemidef) :
    Tendsto (fun n => cavityGaussianMarkedLaw (Q n)) atTop
      (𝓝 (cavityGaussianMarkedLaw Q₀)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  simp_rw [cavityGaussianMarkedLaw_integral _ _ F.continuous.measurable
    (fun x => F.norm_coe_le_norm x)]
  exact cavity_gaussian_joint_expectation_tendsto Q Q₀ hQ hS hS₀ F

end InvariantIsing

end

end OAI
