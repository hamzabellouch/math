import OAI.Probability.InvariantIsing.Magnetic.RestrictedPairMoments

namespace OAI

/-! One-step recursion for the actual constrained one- and two-spin means. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma integrable_restrictedCoordinateMean {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (j : Fin N) (μ : Measure (Fin N → ℝ)) [IsFiniteMeasure μ] :
    Integrable (restrictedCoordinateMean hN S hS n b v hb j) μ := by
  apply Integrable.of_bound (measurable_restrictedCoordinateMean hN S hS n b v hb j).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun z => by
    simpa only [Real.norm_eq_abs] using restrictedCoordinateMean_bound hN S hS n b v hb j z)

lemma integrable_restrictedPairCoordinateMean {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ j < n, 0 < b j) (i : Fin (n + 1)) (j : Fin N)
    (μ : Measure (Fin N → ℝ)) [IsFiniteMeasure μ] :
    Integrable (restrictedPairCoordinateMean hN S hS n b v hb i j) μ := by
  apply Integrable.of_bound (measurable_restrictedPairCoordinateMean hN S hS n b v hb i j).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun z => by
    simpa only [Real.norm_eq_abs] using restrictedPairCoordinateMean_bound hN S hS n b v hb i j z)

lemma restrictedCoordinateMean_succ {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n + 1, 0 < b i) (j : Fin N) (z : Fin N → ℝ) :
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    let hbs := fun i hi => hb (i + 1) (by omega)
    restrictedCoordinateMean hN S hS (n + 1) b v hb j z =
      ∫ y, restrictedCoordinateMean hN S hS n bs vs hbs j y
        ∂vectorGaussianTransition N (b 0) (v 0) (restrictedFieldRecursion S n bs vs)
          (restrictedFieldRecursion_regular hN S hS n bs vs hbs).1 z := by
  dsimp only
  change (∫ σ : Spin N, spinValue (σ j) ∂(_ ∘ₖ _) z) = _
  rw [Kernel.integral_comp (Integrable.of_finite)]
  rfl

lemma restrictedPairCoordinateMean_succ {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ j < n + 1, 0 < b j) (i : Fin (n + 1)) (j : Fin N) (z : Fin N → ℝ) :
    let bs := fun k => b (k + 1)
    let vs := fun k => v (k + 1)
    let hbs := fun k hk => hb (k + 1) (by omega)
    restrictedPairCoordinateMean hN S hS (n + 1) b v hb i.succ j z =
      ∫ y, restrictedPairCoordinateMean hN S hS n bs vs hbs i j y
        ∂vectorGaussianTransition N (b 0) (v 0) (restrictedFieldRecursion S n bs vs)
          (restrictedFieldRecursion_regular hN S hS n bs vs hbs).1 z := by
  dsimp only
  change (∫ σ : Spin N × Spin N, spinValue (σ.1 j) * spinValue (σ.2 j) ∂(_ ∘ₖ _) z) = _
  rw [Kernel.integral_comp (Integrable.of_finite)]
  rfl

end InvariantIsing

end

end OAI
