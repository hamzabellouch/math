import OAI.Probability.InvariantIsing.Cavity.CavityRootedReplicaTransport
import OAI.Probability.InvariantIsing.Cavity.CavityInnovationPrefix

namespace OAI

/-! The common-depth spin observable survives the full rooted quadratic
innovation change, including the disorder and all replica normalizations. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityRootedSpinDepthTest {d k n : ℕ} (a : ℕ → ℝ) (j : Fin k)
    (σ : ℕ → CavitySpinState d k n) : ℝ :=
  a (cavityCommonMarkDepth n (σ 0).1.2.1 (σ 1).1.2.1) *
    (spinValue ((σ 0).2 j) * spinValue ((σ 1).2 j))

lemma measurable_cavityRootedSpinDepthTest {d k n : ℕ} (a : ℕ → ℝ) (j : Fin k) :
    Measurable (cavityRootedSpinDepthTest (d := d) (n := n) a j) := by
  have hc : Measurable (fun σ : ℕ → CavitySpinState d k n =>
      cavityCommonMarkDepth n (σ 0).1.2.1 (σ 1).1.2.1) :=
    (cavityCommonMarkDepth_measurable n).comp
      (show Measurable (fun σ : ℕ → CavitySpinState d k n =>
        ((σ 0).1.2.1, (σ 1).1.2.1)) from by fun_prop)
  have hs (i : ℕ) : Measurable (fun σ : ℕ → CavitySpinState d k n =>
      spinValue ((σ i).2 j)) :=
    (measurable_of_finite (fun ε : Spin k => spinValue (ε j))).comp (by fun_prop)
  exact ((measurable_of_countable a).comp hc).mul ((hs 0).mul (hs 1))

lemma cavityRootedSpinDepthTest_innovation {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (hdet : ∀ i, IsUnit (1 - H i * K).det) (a : ℕ → ℝ) (j : Fin k)
    (σ : ℕ → CavitySpinState d k n)
    (hroot : (σ 0).1.1 = (σ 1).1.1) :
    cavityRootedSpinDepthTest a j (fun i => cavityRootedSpinInnovation n K H b (σ i)) =
      cavityRootedSpinDepthTest a j σ := by
  unfold cavityRootedSpinDepthTest cavityRootedSpinInnovation cavityResidualInnovationMap
  dsimp only
  rw [← hroot, cavityQuadraticInnovation_commonMarkDepth n K H _ hdet]

lemma cavityRootedFullGibbs_root_ae {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (he : Integrable (fun z => Real.exp (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
      ((cavityRootedPriorKernel n R ω).prod π)) :
    ∀ᵐ z ∂cavityRootedFullGibbs n K R L C π ω, z.1.1 = ω.1 := by
  rw [cavityRootedFullGibbs_eq_residual_map n K R L C π ω.1 ω.2 he]
  apply (ae_map_iff (measurable_cavityAttachSpinRoot n ω.1).aemeasurable
    (measurableSet_eq_fun (by fun_prop) measurable_const)).mpr
  exact ae_of_all _ fun _ => rfl

lemma cavity_rooted_replicas_same_root {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (P : Measure (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n))
    (hI : ∀ᵐ ω ∂P, Integrable
      (fun z => Real.exp (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
      ((cavityRootedPriorKernel n R ω).prod π)) :
    ∀ᵐ σ ∂((probabilityReplicaKernel (cavityRootedFullGibbs n K R L C π)
      (cavityRootedFullGibbs n K R L C π).measurable) ∘ₘ P),
        (σ 0).1.1 = (σ 1).1.1 := by
  apply Measure.ae_comp_of_ae_ae (measurableSet_eq_fun (by fun_prop) (by fun_prop))
  filter_upwards [hI] with ω hω
  have hr := cavityRootedFullGibbs_root_ae n K R L C π ω hω
  have h0 := (measurePreserving_eval_infinitePi
    (fun _ : ℕ => cavityRootedFullGibbs n K R L C π ω) 0).quasiMeasurePreserving.ae hr
  have h1 := (measurePreserving_eval_infinitePi
    (fun _ : ℕ => cavityRootedFullGibbs n K R L C π ω) 1).quasiMeasurePreserving.ae hr
  filter_upwards [h0, h1] with σ hσ0 hσ1
  exact hσ0.trans hσ1.symm

theorem cavity_rooted_spin_depth_test_transport {d k : ℕ} (n : ℕ)
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
    (π : Measure (Spin k)) [IsProbabilityMeasure π] (a : ℕ → ℝ) (j : Fin k) :
    let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)
    let J₀ := (1 - H 0 * K)⁻¹
    let P' := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (J₀ * S₀ * J₀.transpose)).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b
        (cavityGaussianMarks (fun i =>
          (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose)) : Measure _)
    (∫ σ, cavityRootedSpinDepthTest a j σ
      ∂((probabilityReplicaKernel (cavityRootedFullGibbs n K (H n) L C π)
        (cavityRootedFullGibbs n K (H n) L C π).measurable) ∘ₘ P)) =
    ∫ σ, cavityRootedSpinDepthTest a j σ
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
  have htest := measurable_cavityRootedSpinDepthTest (d := d) (n := n) a j
  rw [← hm, integral_map hT.aemeasurable htest.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hr] with σ hσ
  exact (cavityRootedSpinDepthTest_innovation n K H b hdet a j σ hσ).symm

end InvariantIsing

end

end OAI
