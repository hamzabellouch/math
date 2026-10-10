import OAI.Probability.InvariantIsing.Fields.PriorFieldLogNormalizer
import OAI.Probability.InvariantIsing.Magnetic.RestrictedSpinPrior
import OAI.Probability.InvariantIsing.Magnetic.RestrictedFieldRecursion

namespace OAI

/-! The constrained block's actual logarithmic normalizer, with the
original cube mass retained, equals its vector Gaussian recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal BigOperators

namespace InvariantIsing

lemma restricted_vector_recursion_const_add {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (a : ℝ) (z : Fin N → ℝ) :
    cascadeRecursion n b (fun i => vectorGaussianLaw N (v i)) (fun _ p => p.1 + p.2)
      (fun y => a + restrictedFieldTerminal S y) z = a + restrictedFieldRecursion S n b v z := by
  induction n generalizing b v z with
  | zero => rfl
  | succ n ih =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    have hbs : ∀ i < n, 0 < bs i := fun i hi => hb (i + 1) (by omega)
    change logMean (b 0) (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ))
      (fun w => cascadeRecursion n bs (fun i => vectorGaussianLaw N (vs i))
        (fun _ p => p.1 + p.2) (fun y => a + restrictedFieldTerminal S y) (z + w)) =
      a + logMean (b 0) (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ))
        (fun w => restrictedFieldRecursion S n bs vs (z + w))
    simp_rw [ih bs vs hbs]
    exact logMean_const_add _ (hb 0 (by omega)).ne'
      (integrable_exp_restrictedFieldRecursion hN S hS n bs vs hbs (v 0) (b 0) z) a

lemma restricted_normalized_field_recursion {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (z : Fin N → ℝ) :
    cascadeRecursion n b (fun i => vectorGaussianLaw N (v i)) (fun _ p => p.1 + p.2)
      (fun y => finiteLogIntegral (restrictedSpinPrior S hS : Measure (Spin N)) (fieldEnergy y)) z =
      restrictedFieldRecursion S n b v z - (Real.log S.card - N * Real.log 2) := by
  have he : (fun y => finiteLogIntegral (restrictedSpinPrior S hS : Measure (Spin N)) (fieldEnergy y)) =
      fun y => -(Real.log S.card - N * Real.log 2) + restrictedFieldTerminal S y := by
    funext y
    rw [finiteLogIntegral_restrictedSpinPrior]
    unfold restrictedFieldTerminal
    ring
  rw [he, restricted_vector_recursion_const_add hN S hS n b v hb]
  ring

def restrictedFieldVectorLogNormalizer {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (h : FieldStep) (z : Fin N → ℝ)
    (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) : ℝ :=
  priorFieldVectorLogNormalizer N (restrictedSpinPrior S hS : Measure (Spin N)) h z p +
    (Real.log S.card - N * Real.log 2)

lemma measurable_restrictedFieldVectorLogNormalizer {N : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) :
    Measurable (fun p : (Fin N → ℝ) ×
      (LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) =>
        restrictedFieldVectorLogNormalizer S hS h p.1 p.2) :=
  (measurable_priorFieldVectorLogNormalizer N (restrictedSpinPrior S hS : Measure (Spin N)) h).add_const _

lemma restricted_normalized_root_integral {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (root : ℝ≥0) :
    (∫ z, cascadeRecursion h.depth (chainExponent h.cut)
      (fun i => vectorGaussianLaw N (fieldStepVariance h i)) (fun _ p => p.1 + p.2)
      (fun y => finiteLogIntegral (restrictedSpinPrior S hS : Measure (Spin N)) (fieldEnergy y)) z
      ∂(vectorGaussianLaw N root : Measure (Fin N → ℝ))) =
      (∫ z, restrictedFieldRecursion S h.depth (chainExponent h.cut) (fieldStepVariance h) z
        ∂(vectorGaussianLaw N root : Measure (Fin N → ℝ))) - (Real.log S.card - N * Real.log 2) := by
  have hb : ∀ i < h.depth, 0 < chainExponent h.cut i :=
    fun i hi => ((chainExponent_admissible h.ordered_cut h.first h.last).1 i hi).1
  have he := fun z => restricted_normalized_field_recursion hN S hS h.depth
    (chainExponent h.cut) (fieldStepVariance h) hb z
  simp_rw [he]
  rw [integral_sub (restrictedFieldRecursion_root_integrable hN S hS h.depth
    (chainExponent h.cut) (fieldStepVariance h) hb root) (integrable_const _)]
  simp

lemma integrable_restrictedFieldVectorLogNormalizer {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (root : ℝ≥0) :
    Integrable (fun p => restrictedFieldVectorLogNormalizer S hS h p.1 p.2)
      ((vectorGaussianLaw N root : Measure (Fin N → ℝ)).prod (fieldVectorCoordinateLaw N h)) := by
  have hi := (prior_field_vector_log_root_integral N
    (restrictedSpinPrior S hS : Measure (Spin N)) hN h root).1
  exact hi.add (integrable_const _)

theorem restricted_field_vector_log_root_integral {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (root : ℝ≥0) :
    Integrable (fun p => restrictedFieldVectorLogNormalizer S hS h p.1 p.2)
      ((vectorGaussianLaw N root : Measure (Fin N → ℝ)).prod (fieldVectorCoordinateLaw N h)) ∧
    (∫ p, restrictedFieldVectorLogNormalizer S hS h p.1 p.2
      ∂(vectorGaussianLaw N root : Measure (Fin N → ℝ)).prod (fieldVectorCoordinateLaw N h)) =
      ∫ z, restrictedFieldRecursion S h.depth (chainExponent h.cut) (fieldStepVariance h) z
        ∂(vectorGaussianLaw N root : Measure (Fin N → ℝ)) := by
  refine ⟨integrable_restrictedFieldVectorLogNormalizer hN S hS h root, ?_⟩
  have hh := prior_field_vector_log_root_integral N (restrictedSpinPrior S hS : Measure (Spin N)) hN h root
  simp only [restrictedFieldVectorLogNormalizer]
  rw [integral_add hh.1 (integrable_const _), hh.2,
    restricted_normalized_root_integral hN S hS h root]
  simp

end InvariantIsing

end

end OAI
