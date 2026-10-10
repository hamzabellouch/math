import OAI.Probability.InvariantIsing.Cavity.CavityRootedSpinTestTransport

namespace OAI

/-! Disintegration of the bounded common-depth spin test over its actual
Gaussian-root and cascade disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavityRootedSpinTestMean {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (a : ℕ → ℝ) (j : Fin k)
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) : ℝ :=
  ∫ σ, cavityRootedSpinDepthTest a j σ
    ∂Measure.infinitePi (fun _ : ℕ => cavityRootedFullGibbs n K R L C π ω)

lemma measurable_cavityRootedSpinTestMean {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (a : ℕ → ℝ) (j : Fin k) :
    Measurable (cavityRootedSpinTestMean n K R L C π a j) := by
  let κ := probabilityReplicaKernel (cavityRootedFullGibbs n K R L C π)
    (cavityRootedFullGibbs n K R L C π).measurable
  exact (((measurable_cavityRootedSpinDepthTest (d := d) (n := n) a j).comp
    measurable_snd).stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

lemma cavityRootedSpinDepthTest_abs_le {d k n : ℕ} (a : ℕ → ℝ) (j : Fin k)
    {B : ℝ} (ha : ∀ i, |a i| ≤ B) (σ : ℕ → CavitySpinState d k n) :
    |cavityRootedSpinDepthTest a j σ| ≤ B := by
  simpa only [cavityRootedSpinDepthTest, abs_mul, abs_spinValue, mul_one, one_mul] using
    ha (cavityCommonMarkDepth n (σ 0).1.2.1 (σ 1).1.2.1)

lemma cavityRootedSpinTestMean_abs_le {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (a : ℕ → ℝ) (j : Fin k) {B : ℝ} (ha : ∀ i, |a i| ≤ B)
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) :
    |cavityRootedSpinTestMean n K R L C π a j ω| ≤ B :=
  abs_integral_le_const_of_bound (measurable_cavityRootedSpinDepthTest a j)
    (cavityRootedSpinDepthTest_abs_le a j ha)

theorem cavity_rooted_spin_test_disintegration {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (P : Measure (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n))
    [IsProbabilityMeasure P] (a : ℕ → ℝ) (j : Fin k)
    {B : ℝ} (ha : ∀ i, |a i| ≤ B) :
    (∫ σ, cavityRootedSpinDepthTest a j σ
      ∂((probabilityReplicaKernel (cavityRootedFullGibbs n K R L C π)
        (cavityRootedFullGibbs n K R L C π).measurable) ∘ₘ P)) =
      ∫ ω, cavityRootedSpinTestMean n K R L C π a j ω ∂P := by
  have hi := integrable_of_measurable_abs_le
    (μ := (probabilityReplicaKernel (cavityRootedFullGibbs n K R L C π)
      (cavityRootedFullGibbs n K R L C π).measurable) ∘ₘ P)
    (measurable_cavityRootedSpinDepthTest (d := d) (n := n) a j)
    (cavityRootedSpinDepthTest_abs_le a j ha)
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  simpa only [Kernel.const_apply, probabilityReplicaKernel, Kernel.coe_mk,
    cavityRootedSpinTestMean] using
    Kernel.integral_comp hi

theorem cavity_rooted_spin_test_product_disintegration {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (Q : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n)) [IsProbabilityMeasure Q]
    (a : ℕ → ℝ) (j : Fin k) {B : ℝ} (ha : ∀ i, |a i| ≤ B) :
    (∫ σ, cavityRootedSpinDepthTest a j σ
      ∂((probabilityReplicaKernel (cavityRootedFullGibbs n K R L C π)
        (cavityRootedFullGibbs n K R L C π).measurable) ∘ₘ P.prod Q)) =
      ∫ s, ∫ V, cavityRootedSpinTestMean n K R L C π a j (s, V) ∂Q ∂P := by
  rw [cavity_rooted_spin_test_disintegration n K R L C π (P.prod Q) a j ha]
  exact integral_prod _ (integrable_of_measurable_abs_le
    (measurable_cavityRootedSpinTestMean n K R L C π a j)
    (cavityRootedSpinTestMean_abs_le n K R L C π a j ha))

end InvariantIsing

end

end OAI
