import OAI.Probability.InvariantIsing.Cavity.CavityRootedDepthTransport
import OAI.Probability.InvariantIsing.Cavity.CavityRootedTestMean

namespace OAI

/-! The bounded common-depth observable disintegrated over root and forest. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavityRootedDepthTestMean {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (a : ℕ → ℝ)
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) : ℝ :=
  ∫ σ, cavityRootedDepthTest a σ
    ∂Measure.infinitePi (fun _ : ℕ => cavityRootedFullGibbs n K R L C π ω)

lemma measurable_cavityRootedDepthTestMean {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (a : ℕ → ℝ) :
    Measurable (cavityRootedDepthTestMean n K R L C π a) := by
  let κ := probabilityReplicaKernel (cavityRootedFullGibbs n K R L C π)
    (cavityRootedFullGibbs n K R L C π).measurable
  exact (((measurable_cavityRootedDepthTest (d := d) (k := k) (n := n) a).comp
    measurable_snd).stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

lemma cavityRootedDepthTest_abs_le {d k n : ℕ} (a : ℕ → ℝ)
    {B : ℝ} (ha : ∀ i, |a i| ≤ B) (σ : ℕ → CavitySpinState d k n) :
    |cavityRootedDepthTest a σ| ≤ B := by
  simpa only [cavityRootedDepthTest, abs_mul, abs_spinValue, mul_one, one_mul] using
    ha (cavityCommonMarkDepth n (σ 0).1.2.1 (σ 1).1.2.1)

lemma cavityRootedDepthTestMean_abs_le {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (a : ℕ → ℝ) {B : ℝ} (ha : ∀ i, |a i| ≤ B)
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) :
    |cavityRootedDepthTestMean n K R L C π a ω| ≤ B :=
  abs_integral_le_const_of_bound (measurable_cavityRootedDepthTest a)
    (cavityRootedDepthTest_abs_le a ha)

theorem cavity_rooted_depth_test_disintegration {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (P : Measure (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n))
    [IsProbabilityMeasure P] (a : ℕ → ℝ)
    {B : ℝ} (ha : ∀ i, |a i| ≤ B) :
    (∫ σ, cavityRootedDepthTest a σ
      ∂((probabilityReplicaKernel (cavityRootedFullGibbs n K R L C π)
        (cavityRootedFullGibbs n K R L C π).measurable) ∘ₘ P)) =
      ∫ ω, cavityRootedDepthTestMean n K R L C π a ω ∂P := by
  have hi := integrable_of_measurable_abs_le
    (μ := (probabilityReplicaKernel (cavityRootedFullGibbs n K R L C π)
      (cavityRootedFullGibbs n K R L C π).measurable) ∘ₘ P)
    (measurable_cavityRootedDepthTest (d := d) (k := k) (n := n) a)
    (cavityRootedDepthTest_abs_le a ha)
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  simpa only [Kernel.const_apply, probabilityReplicaKernel, Kernel.coe_mk,
    cavityRootedDepthTestMean] using
    Kernel.integral_comp hi

theorem cavity_rooted_depth_test_product_disintegration {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (Q : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n)) [IsProbabilityMeasure Q]
    (a : ℕ → ℝ) {B : ℝ} (ha : ∀ i, |a i| ≤ B) :
    (∫ σ, cavityRootedDepthTest a σ
      ∂((probabilityReplicaKernel (cavityRootedFullGibbs n K R L C π)
        (cavityRootedFullGibbs n K R L C π).measurable) ∘ₘ P.prod Q)) =
      ∫ s, ∫ V, cavityRootedDepthTestMean n K R L C π a (s, V) ∂Q ∂P := by
  rw [cavity_rooted_depth_test_disintegration n K R L C π (P.prod Q) a ha]
  exact integral_prod _ (integrable_of_measurable_abs_le
    (measurable_cavityRootedDepthTestMean n K R L C π a)
    (cavityRootedDepthTestMean_abs_le n K R L C π a ha))

end InvariantIsing

end

end OAI
