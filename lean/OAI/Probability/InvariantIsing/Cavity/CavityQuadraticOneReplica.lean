import OAI.Probability.InvariantIsing.Cavity.CavityOneReplicaGaussian
import OAI.Probability.InvariantIsing.Cavity.CavityInnovationCovariancePositive

namespace OAI

/-! The actual one-replica marginal after the quadratic cavity tilt. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityQuadraticResidualKernel {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (s : EuclideanSpace ℝ (Fin d)) :
    Kernel (NoiseTree (EuclideanSpace ℝ (Fin d)) n)
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) :=
  ⟨cavityQuadraticResidualGibbs n K R s, measurable_cavityQuadraticResidualGibbs n K R s⟩

instance cavityQuadraticResidualKernel_markov {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (s : EuclideanSpace ℝ (Fin d)) :
    IsMarkovKernel (cavityQuadraticResidualKernel n K R s) := by
  constructor
  intro V
  change IsProbabilityMeasure (cavityQuadraticResidualGibbs n K R s V)
  infer_instance

lemma cavity_residual_innovation_sum {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (b : ℕ → ℝ) (s : EuclideanSpace ℝ (Fin d))
    (p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) :
    cavityLeafSum n (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹ s)
        (cavityResidualInnovationMap n K H b s p).1 +
      (cavityResidualInnovationMap n K H b s p).2 = cavityLeafSum n s p.1 + p.2 := by
  dsimp only [cavityResidualInnovationMap]
  rw [cavityInnovationLeaf_sum]
  abel

theorem cavity_quadratic_one_transport {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ)
    (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (hbCascade : CascadeExponents n b)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
    (hR : (H n).PosSemidef)
    (hQR : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) :
    (cavityQuadraticResidualKernel n K (H n) s ∘ₘ
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)).map
        (cavityResidualInnovationMap n K H b s) =
      ((markedReplicaLaw n b (cavityGaussianMarks (fun i =>
        (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose))).map (fun σ => σ 0)).prod
        (multivariateGaussian 0 (cavityResolvent K (H n))) := by
  have he := congrArg (fun P : Measure (ℕ → NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      EuclideanSpace ℝ (Fin d)) => P.map (fun σ => σ 0))
    (cavity_quadratic_residual_replica_law n K H S b hbCascade hK hH hS hb hdet hΔ hQ hR hQR s)
  rw [Measure.map_map (measurable_pi_apply 0) (by
      apply Measurable.of_eval
      intro i
      exact (measurable_cavityResidualInnovationMap n K H b s).comp (measurable_pi_apply i)),
    Measure.map_map (measurable_pi_apply 0) (by fun_prop)] at he
  change ((probabilityReplicaKernel (cavityQuadraticResidualKernel n K (H n) s)
    (cavityQuadraticResidualKernel n K (H n) s).measurable ∘ₘ _).map
      (cavityResidualInnovationMap n K H b s ∘ (fun σ => σ 0))) = _ at he
  rw [← Measure.map_map (measurable_cavityResidualInnovationMap n K H b s)
      (measurable_pi_apply 0), cavity_replica_one_marginal] at he
  simp only [Function.comp_def] at he
  rw [show (fun p : (ℕ → NoiseLeaf (EuclideanSpace ℝ (Fin d)) n) ×
        (ℕ → EuclideanSpace ℝ (Fin d)) => (fun i => (p.1 i, p.2 i)) 0) =
      Prod.map (fun σ => σ 0) (fun r => r 0) from rfl,
    ← Measure.map_prod_map _ _ (measurable_pi_apply 0) (measurable_pi_apply 0),
    Measure.infinitePi_map_eval] at he
  exact he

theorem cavity_quadratic_one_gaussian {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ)
    (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (hbCascade : CascadeExponents n b)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
    (hR : (H n).PosSemidef)
    (hQR : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) :
    (cavityQuadraticResidualKernel n K (H n) s ∘ₘ
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)).map
        (fun p => cavityLeafSum n s p.1 + p.2) =
      multivariateGaussian (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹ s)
        ((∑ i : Fin n, (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose) +
          cavityResolvent K (H n)) := by
  let S' := fun i => (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose
  let R := cavityResolvent K (H n)
  let a := Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹ s
  have hS' : ∀ i, (S' i).PosSemidef := fun i =>
    cavity_innovation_covariance_posSemidef K (H i) (H (i + 1)) (S i) (hS i)
      (b i) (hdet i) (hdet (i + 1)) (hΔ i) (hQ i)
  have hR' : R.PosSemidef := cavity_tilt_covariance_posSemidef K (H n) hR hQR
  have hsum : ((∑ i : Fin n, S' i) + R).PosSemidef :=
    (Matrix.posSemidef_sum (x := fun i : Fin n => S' i)
      Finset.univ (fun i _ => hS' i)).add hR'
  have hl : Measurable (fun p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      EuclideanSpace ℝ (Fin d) => cavityLeafSum n a p.1 + p.2) :=
    ((measurable_cavityLeafSum n a).comp measurable_fst).add measurable_snd
  have he := congrArg (fun P : Measure (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      EuclideanSpace ℝ (Fin d)) => P.map (fun p => cavityLeafSum n a p.1 + p.2))
    (cavity_quadratic_one_transport n K H S b hbCascade hK hH hS hb hdet hΔ hQ hR hQR s)
  rw [Measure.map_map hl (measurable_cavityResidualInnovationMap n K H b s)] at he
  dsimp only [a] at he
  simp only [Function.comp_def, cavity_residual_innovation_sum] at he
  rw [he]
  have hp := Measure.map_prod_map (markedReplicaLaw n b (cavityGaussianMarks S'))
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R) (measurable_pi_apply 0) measurable_id
  rw [Measure.map_id] at hp
  rw [hp, Measure.map_map hl (by fun_prop)]
  change ((markedReplicaLaw n b (cavityGaussianMarks S')).prod (multivariateGaussian 0 R)).map
    (fun p => cavityLeafSum n a (p.1 0) + p.2) = _
  have hadd : (fun p : (ℕ → NoiseLeaf (EuclideanSpace ℝ (Fin d)) n) ×
      EuclideanSpace ℝ (Fin d) => cavityLeafSum n a (p.1 0) + p.2) =
      (fun z => a + z) ∘ (fun p => cavityLeafSum n 0 (p.1 0) + p.2) := by
    funext p
    simp only [Function.comp_def, cavityLeafSum_eq_mark_sum, zero_add]
    abel
  rw [hadd,
    ← Measure.map_map (by fun_prop) (by
      exact ((measurable_cavityLeafSum n 0).comp
        ((measurable_pi_apply 0).comp measurable_fst)).add measurable_snd),
    cavity_marked_leaf_residual_law n b hbCascade S' hS' R hR']
  simpa using cavity_multivariateGaussian_affine_image (1 : Matrix (Fin d) (Fin d) ℝ)
    ((∑ i : Fin n, S' i) + R) hsum 0 a

end InvariantIsing

end

end OAI
