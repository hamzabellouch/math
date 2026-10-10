import OAI.Probability.InvariantIsing.Cavity.CavityInnovationKernel
import OAI.Probability.InvariantIsing.Cavity.CavityQuadraticNormalizer
import OAI.Probability.IsingPerceptron.SamplingIndependent

namespace OAI

/-! Joint replica sampling after the finite quadratic change of measure. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavityQuadratic_terminalGibbsLaw {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (b : ℕ → ℝ) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n) :
    noiseTerminalGibbsLaw n (cavityQuadraticValue n K H b) (fun _ p => p.1 + p.2) s V =
      noiseTiltedLeafLaw n (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
        (fun _ p => p.1 + p.2) s V := by
  have hu : ∀ i : ℕ, Measurable
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.1 + p.2) :=
    fun _ => measurable_fst.add measurable_snd
  rw [noiseTerminalGibbsLaw_eq_tilted n
    (fun i => measurable_cavityQuadraticValue n K H b i) hu s V]
  have he : (fun i (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
      Real.exp (cavityQuadraticValue n K H b (i + 1) (p.1 + p.2) -
        cavityQuadraticValue n K H b i p.1)) =
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i)) := by
    funext i p
    exact (cavityQuadraticStepWeight_telescoping n K H b i p.1 p.2).symm
  rw [he]

theorem cavity_innovation_replica_law {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b)
    (μ ν : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (g : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hc : ∀ i, Measurable (c i)) (hg : ∀ i, Measurable (g i))
    (hcpos : ∀ i s a, 0 < c i (s, a))
    (hν : ∀ i s, (((μ i : Measure (EuclideanSpace ℝ (Fin d))).withDensity
      (fun a => ENNReal.ofReal (c i (s, a) ^ b i))).map (fun a => g i (s, a))) =
        (ν i : Measure (EuclideanSpace ℝ (Fin d)))) (s : EuclideanSpace ℝ (Fin d)) :
    ((probabilityReplicaKernel (noiseTiltedLeafLaw n c (fun _ p => p.1 + p.2) s)
      (measurable_noiseTiltedLeafLaw n hc (fun _ => measurable_fst.add measurable_snd) s)) ∘ₘ
        (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b μ : Measure _)).map
      (fun σ i => cavityInnovationLeaf n c g s (σ i)) = markedReplicaLaw n b ν := by
  have hu : ∀ i : ℕ, Measurable
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.1 + p.2) :=
    fun _ => measurable_fst.add measurable_snd
  have hm (i : ℕ) (u : EuclideanSpace ℝ (Fin d)) :
      (∫⁻ a, ENNReal.ofReal (c i (u, a) ^ b i) ∂(μ i : Measure _)) = 1 := by
    have h := congrArg (fun η : Measure (EuclideanSpace ℝ (Fin d)) => η Set.univ) (hν i u)
    rw [Measure.map_apply
      (show Measurable (fun a => g i (u, a)) from
        (hg i).comp (measurable_const.prodMk measurable_id))
      MeasurableSet.univ, Set.preimage_univ, withDensity_apply _ MeasurableSet.univ,
      setLIntegral_univ, measure_univ] at h
    exact h
  have hT : Measurable (cavityInnovationTree n b μ c g s) :=
    (measurable_cavityInnovationTree n b μ c g hc hg).comp
      (measurable_const.prodMk measurable_id)
  have hL : Measurable (cavityInnovationLeaf n c g s) :=
    (measurable_cavityInnovationLeaf n c g hc hg).comp
      (measurable_const.prodMk measurable_id)
  apply cavity_replica_kernel_transport
    (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b μ : Measure _)
    (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b ν : Measure _)
    (ν := noiseTiltedLeafLaw n c (fun _ p => p.1 + p.2) s)
    (κ := fun V => noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V)
    (measurable_noiseTiltedLeafLaw n hc hu s) (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n).measurable
    hT (cavityInnovationTree_law n b μ ν c g hc hg hcpos hν s) hL
  filter_upwards [noiseGibbsRegular_ae n b hb μ hc hu hcpos hm s] with V hV
  exact cavityInnovationLeaf_tilted_law n b μ c g hc hg hcpos s V hV

theorem cavity_quadratic_replica_innovation_law {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ)
    (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (hbCascade : CascadeExponents n b)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) :
    let μ := cavityGaussianMarks S
    let c := fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i)
    let g := fun i => cavityStepInnovation K (H i) (H (i + 1))
    let hu : ∀ _i : ℕ, Measurable
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.1 + p.2) :=
      fun _ => measurable_fst.add measurable_snd
    let hc := fun i => measurable_cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i)
    ((probabilityReplicaKernel (noiseTiltedLeafLaw n c (fun _ p => p.1 + p.2) s)
      (measurable_noiseTiltedLeafLaw n hc hu s)) ∘ₘ
        (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b μ : Measure _)).map
      (fun σ i => cavityInnovationLeaf n c g s (σ i)) =
      markedReplicaLaw n b (cavityGaussianMarks (fun i =>
        (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose)) := by
  dsimp only
  apply cavity_innovation_replica_law n b hbCascade
  · intro i
    exact measurable_cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i)
  · intro i
    exact measurable_cavityStepInnovation K (H i) (H (i + 1))
  · intro i u a
    exact cavityQuadraticStepWeight_pos K (H i) (H (i + 1)) (b i) (u, a)
  · intro i u
    exact cavity_quadratic_step_weight_innovation_law K (H i) (H (i + 1)) (S i)
      hK (hH (i + 1)) (hS i) (b i) (hb i) (hdet i) (hdet (i + 1))
      (hΔ i) (hQ i) u

/-- The entire sampled innovation path has the independent-mark cascade
law, with the common-prefix dependence carried only by the sampled leaves. -/
theorem cavity_innovation_mark_path_law {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b)
    (μ ν : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (g : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hc : ∀ i, Measurable (c i)) (hg : ∀ i, Measurable (g i))
    (hcpos : ∀ i s a, 0 < c i (s, a))
    (hν : ∀ i s, (((μ i : Measure (EuclideanSpace ℝ (Fin d))).withDensity
      (fun a => ENNReal.ofReal (c i (s, a) ^ b i))).map (fun a => g i (s, a))) =
        (ν i : Measure (EuclideanSpace ℝ (Fin d)))) (s : EuclideanSpace ℝ (Fin d)) :
    ((probabilityReplicaKernel (noiseTiltedLeafLaw n c (fun _ p => p.1 + p.2) s)
      (measurable_noiseTiltedLeafLaw n hc (fun _ => measurable_fst.add measurable_snd) s)) ∘ₘ
        (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b μ : Measure _)).map
      (fun σ => replicaMarkPath n (fun i => cavityInnovationLeaf n c g s (σ i))) =
      ((cascadeReplicaLaw n b).prod (Measure.infinitePi
        (fun v : ForestVertex n => (ν (forestVertexDepth n v) : Measure _)))).map
          (coordinateMarkPath n) := by
  have hmap : Measurable (fun σ : ℕ → NoiseLeaf (EuclideanSpace ℝ (Fin d)) n =>
      fun i => cavityInnovationLeaf n c g s (σ i)) := by
    apply Measurable.of_eval
    intro i
    exact ((measurable_cavityInnovationLeaf n c g hc hg).comp
      (measurable_const.prodMk measurable_id)).comp (measurable_pi_apply i)
  change Measure.map ((replicaMarkPath n) ∘
    (fun σ : ℕ → NoiseLeaf (EuclideanSpace ℝ (Fin d)) n =>
      fun i => cavityInnovationLeaf n c g s (σ i))) _ = _
  rw [← Measure.map_map (measurable_replicaMarkPath n) hmap,
    cavity_innovation_replica_law n b hb μ ν c g hc hg hcpos hν s]
  exact marked_path_law n b hb ν

end InvariantIsing

end

end OAI
