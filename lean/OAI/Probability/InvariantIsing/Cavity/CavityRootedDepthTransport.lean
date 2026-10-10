import OAI.Probability.InvariantIsing.Cavity.CavityRootedSpinTestTransport

namespace OAI

/-! Common depths alone are preserved by the same-root quadratic innovation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityRootedDepthTest {d k n : ℕ} (a : ℕ → ℝ)
    (σ : ℕ → CavitySpinState d k n) : ℝ :=
  a (cavityCommonMarkDepth n (σ 0).1.2.1 (σ 1).1.2.1)

lemma measurable_cavityRootedDepthTest {d k n : ℕ} (a : ℕ → ℝ) :
    Measurable (cavityRootedDepthTest (d := d) (k := k) (n := n) a) := by
  have hc : Measurable (fun σ : ℕ → CavitySpinState d k n =>
      cavityCommonMarkDepth n (σ 0).1.2.1 (σ 1).1.2.1) :=
    (cavityCommonMarkDepth_measurable n).comp
      (show Measurable (fun σ : ℕ → CavitySpinState d k n =>
        ((σ 0).1.2.1, (σ 1).1.2.1)) from by fun_prop)
  exact (measurable_of_countable a).comp hc

lemma cavityRootedDepthTest_innovation {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (hdet : ∀ i, IsUnit (1 - H i * K).det) (a : ℕ → ℝ)
    (σ : ℕ → CavitySpinState d k n)
    (hroot : (σ 0).1.1 = (σ 1).1.1) :
    cavityRootedDepthTest a (fun i => cavityRootedSpinInnovation n K H b (σ i)) =
      cavityRootedDepthTest a σ := by
  unfold cavityRootedDepthTest cavityRootedSpinInnovation cavityResidualInnovationMap
  dsimp only
  rw [← hroot, cavityQuadraticInnovation_commonMarkDepth n K H _ hdet]

theorem cavity_rooted_depth_test_transport {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (hbCascade : CascadeExponents n b)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
    (hR : (H n).PosSemidef)
    (hQR : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] (a : ℕ → ℝ) :
    let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)
    let J₀ := (1 - H 0 * K)⁻¹
    let P' := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (J₀ * S₀ * J₀.transpose)).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b
        (cavityGaussianMarks (fun i =>
          (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose)) : Measure _)
    (∫ σ, cavityRootedDepthTest a σ
      ∂((probabilityReplicaKernel (cavityRootedFullGibbs n K (H n) L C π)
        (cavityRootedFullGibbs n K (H n) L C π).measurable) ∘ₘ P)) =
    ∫ σ, cavityRootedDepthTest a σ
      ∂((probabilityReplicaKernel (cavityRootedFullGibbs n 0 (cavityResolvent K (H n)) L C π)
        (cavityRootedFullGibbs n 0 (cavityResolvent K (H n)) L C π).measurable) ∘ₘ P') := by
  intro P J₀ P'
  have hm := cavity_rooted_full_replica_transport n K H S b S₀ hS₀ L C
    hbCascade hK hH hS hb hdet hΔ hQ hR hQR π
  have hi := (cavity_rooted_full_integrability n K H S b S₀ hS₀ L C
    hbCascade hK hH hS hb hdet hΔ hQ hR hQR π).mono (fun _ h => h.2)
  have hr := cavity_rooted_replicas_same_root n K (H n) L C π P hi
  let T : (ℕ → CavitySpinState d k n) → ℕ → CavitySpinState d k n :=
    fun σ i => cavityRootedSpinInnovation n K H b (σ i)
  have hT : Measurable T := Measurable.of_eval fun i =>
    (measurable_cavityRootedSpinInnovation n K H b).comp (measurable_pi_apply i)
  have htest := measurable_cavityRootedDepthTest (d := d) (k := k) (n := n) a
  rw [← hm, integral_map hT.aemeasurable htest.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hr] with σ hσ
  exact (cavityRootedDepthTest_innovation n K H b hdet a σ hσ).symm

end InvariantIsing

end

end OAI
