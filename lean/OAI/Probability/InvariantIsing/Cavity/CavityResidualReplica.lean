import OAI.Probability.InvariantIsing.Cavity.CavityResidualInnovation

namespace OAI

/-! Countably many cavity replicas with one independent terminal Gaussian
residual per replica. The residual family is independent of the whole
innovation cascade, including coincidences of sampled leaves. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

private lemma cavity_measurable_prod_const {Ω X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (κ : Measure Y) [IsProbabilityMeasure κ] :
    Measurable (fun ω => (ν ω).prod κ) := by
  let K : Kernel Ω X := ⟨ν, hν⟩
  have : IsMarkovKernel K := ⟨fun ω => by change IsProbabilityMeasure (ν ω); infer_instance⟩
  have he : (fun ω => (ν ω).prod κ) = K ×ₖ Kernel.const Ω κ := by
    funext ω
    exact (Kernel.prod_apply K (Kernel.const Ω κ) ω).symm
  rw [he]
  exact (K ×ₖ Kernel.const Ω κ).measurable

private lemma cavity_infinitePi_zip {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) (κ : Measure Y) [IsProbabilityMeasure ν] [IsProbabilityMeasure κ] :
    ((Measure.infinitePi (fun _ : ℕ => ν)).prod
      (Measure.infinitePi (fun _ : ℕ => κ))).map (fun p => fun i => (p.1 i, p.2 i)) =
        Measure.infinitePi (fun _ : ℕ => ν.prod κ) := by
  let z : (ℕ → X) × (ℕ → Y) → ℕ → X × Y := fun p i => (p.1 i, p.2 i)
  have hz : Measurable z := by fun_prop
  apply IsProjectiveLimit.unique _ (Measure.isProjectiveLimit_infinitePi (fun _ : ℕ => ν.prod κ))
  intro I
  let e := MeasurableEquiv.arrowProdEquivProdArrow X Y I
  have hfinite : ((Measure.pi (fun _ : I => ν)).prod (Measure.pi (fun _ : I => κ))).map e.symm =
      Measure.pi (fun _ : I => ν.prod κ) := by
    have he := (measurePreserving_arrowProdEquivProdArrow X Y I
      (fun _ : I => ν) (fun _ : I => κ)).map_eq
    rw [← he, Measure.map_map e.symm.measurable e.measurable]
    simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply, Measure.map_id']
  have hrestr : Measurable (fun p : (ℕ → X) × (ℕ → Y) =>
      (I.restrict p.1, I.restrict p.2)) := by fun_prop
  rw [Measure.map_map (Finset.measurable_restrict I) hz]
  have hcomp : I.restrict ∘ z = e.symm ∘ (fun p : (ℕ → X) × (ℕ → Y) =>
      (I.restrict p.1, I.restrict p.2)) := rfl
  rw [hcomp, ← Measure.map_map e.symm.measurable hrestr]
  change (((Measure.infinitePi (fun _ : ℕ => ν)).prod
    (Measure.infinitePi (fun _ : ℕ => κ))).map
      (Prod.map I.restrict I.restrict)).map e.symm = _
  rw [← Measure.map_prod_map _ _ (Finset.measurable_restrict I) (Finset.measurable_restrict I),
    Measure.infinitePi_map_restrict, Measure.infinitePi_map_restrict, hfinite]

private lemma cavity_replica_product_mixture {Ω X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (κ : Measure Y) [IsProbabilityMeasure κ] :
    (probabilityReplicaKernel (fun ω => (ν ω).prod κ)
      (cavity_measurable_prod_const ν hν κ) ∘ₘ P) =
      ((probabilityReplicaKernel ν hν ∘ₘ P).prod
        (Measure.infinitePi (fun _ : ℕ => κ))).map (fun p => fun i => (p.1 i, p.2 i)) := by
  let z : (ℕ → X) × (ℕ → Y) → ℕ → X × Y := fun p i => (p.1 i, p.2 i)
  have hz : Measurable z := by fun_prop
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable,
    lintegral_map hf hz]
  have hpoint (ω : Ω) : (∫⁻ σ, f σ ∂probabilityReplicaKernel
      (fun ω => (ν ω).prod κ) (cavity_measurable_prod_const ν hν κ) ω) =
      ∫⁻ σ, ∫⁻ r, f (z (σ, r)) ∂Measure.infinitePi (fun _ : ℕ => κ)
        ∂probabilityReplicaKernel ν hν ω := by
    change (∫⁻ σ, f σ ∂Measure.infinitePi (fun _ : ℕ => (ν ω).prod κ)) = _
    rw [← cavity_infinitePi_zip (ν ω) κ, lintegral_map hf hz,
      lintegral_prod _ (show AEMeasurable (fun p => f (z p)) _ from (hf.comp hz).aemeasurable)]
    rfl
  simp_rw [hpoint]
  rw [lintegral_prod _ (show AEMeasurable (fun p => f (z p)) _ from (hf.comp hz).aemeasurable)]
  exact (Measure.lintegral_bind (Kernel.aemeasurable _)
    (hf.comp hz).lintegral_prod_right'.aemeasurable).symm

/-- The whole transformed replica sequence is sampled from the independent
innovation tree, together with an independent iid family of ordinary
terminal Gaussian residuals. -/
theorem cavity_quadratic_residual_replica_law {d : ℕ} (n : ℕ)
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
    (probabilityReplicaKernel (cavityQuadraticResidualGibbs n K (H n) s)
      (measurable_cavityQuadraticResidualGibbs n K (H n) s) ∘ₘ
        (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)).map
      (fun σ i => cavityResidualInnovationMap n K H b s (σ i)) =
      ((markedReplicaLaw n b (cavityGaussianMarks (fun i =>
          (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose))).prod
        (Measure.infinitePi (fun _ : ℕ => multivariateGaussian 0 (cavityResolvent K (H n))))).map
          (fun p => fun i => (p.1 i, p.2 i)) := by
  let c := fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i)
  let g := fun i => cavityStepInnovation K (H i) (H (i + 1))
  let μ := cavityGaussianMarks S
  let μ' := cavityGaussianMarks (fun i =>
    (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose)
  let P : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n) := noiseCascadeLaw _ n b μ
  let Q : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n) := noiseCascadeLaw _ n b μ'
  let κ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (cavityResolvent K (H n))
  let ν := cavityQuadraticResidualGibbs n K (H n) s
  let ρ := fun V => (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod κ
  have hc : ∀ i, Measurable (c i) := fun i => measurable_cavityQuadraticStepWeight _ _ _ _
  have hu : ∀ i : ℕ, Measurable
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.1 + p.2) :=
    fun _ => measurable_fst.add measurable_snd
  have hcp : ∀ i u a, 0 < c i (u, a) :=
    fun i u a => cavityQuadraticStepWeight_pos _ _ _ _ (u, a)
  have hm (i : ℕ) (u : EuclideanSpace ℝ (Fin d)) :
      (∫⁻ a, ENNReal.ofReal (c i (u, a) ^ b i) ∂(μ i : Measure _)) = 1 :=
    cavity_quadratic_step_fractional_moment K (H i) (H (i + 1)) (S i)
      hK (hH (i + 1)) (hS i) (b i) (hb i) (hdet i) (hdet (i + 1)) (hΔ i) (hQ i) u
  have hρ : Measurable ρ := cavity_measurable_prod_const
    (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n)
    (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n).measurable κ
  have hT : Measurable (cavityInnovationTree n b μ c g s) :=
    (measurable_cavityInnovationTree n b μ c g hc
      (fun i => measurable_cavityStepInnovation _ _ _)).comp
        (measurable_const.prodMk measurable_id)
  have hpoint : ∀ᵐ V ∂P, (ν V).map (cavityResidualInnovationMap n K H b s) =
      ρ (cavityInnovationTree n b μ c g s V) := by
    filter_upwards [noiseGibbsRegular_ae n b hbCascade μ hc hu hcp hm s,
      cavity_residual_partition_pos_finite n K H S b hbCascade hK hH hS hb hdet hΔ hQ hR hQR s]
        with V hV hZ
    exact cavity_residual_innovation_leaf_law n K H S b hK hR (hdet n) hQR s V hZ.2 hV
  have he := cavity_replica_kernel_transport P Q
    (ν := ν) (κ := ρ) (measurable_cavityQuadraticResidualGibbs n K (H n) s) hρ
    hT (cavity_quadratic_innovation_tree_law n K H S b hK hH hS hb hdet hΔ hQ s)
    (measurable_cavityResidualInnovationMap n K H b s) hpoint
  change _ = (probabilityReplicaKernel ρ hρ ∘ₘ Q) at he
  rw [he]
  exact cavity_replica_product_mixture Q
    (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n)
    (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n).measurable κ

/-- The independent residual sequence remains independent after the
sampled innovation leaves are represented by their common-prefix paths. -/
theorem cavity_residual_replica_path_law {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (κ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure κ] :
    (((markedReplicaLaw n b μ).prod (Measure.infinitePi (fun _ : ℕ => κ))).map
      (fun p => fun i => (p.1 i, p.2 i))).map
        (fun σ => (replicaMarkPath n (fun i => (σ i).1), fun i => (σ i).2)) =
      (((cascadeReplicaLaw n b).prod (Measure.infinitePi
        (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure _)))).prod
          (Measure.infinitePi (fun _ : ℕ => κ))).map
            (fun p => (coordinateMarkPath n p.1, p.2)) := by
  have hpath : Measurable (fun σ : ℕ → NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      EuclideanSpace ℝ (Fin d) =>
      (replicaMarkPath n (fun i => (σ i).1), fun i => (σ i).2)) :=
    ((measurable_replicaMarkPath n).comp (by fun_prop)).prodMk (by fun_prop)
  rw [Measure.map_map hpath (by fun_prop)]
  change ((markedReplicaLaw n b μ).prod (Measure.infinitePi (fun _ : ℕ => κ))).map
      (Prod.map (replicaMarkPath n) id) =
    (((cascadeReplicaLaw n b).prod (Measure.infinitePi
      (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure _)))).prod
        (Measure.infinitePi (fun _ : ℕ => κ))).map (Prod.map (coordinateMarkPath n) id)
  rw [← Measure.map_prod_map _ _ (measurable_replicaMarkPath n) measurable_id,
    ← Measure.map_prod_map _ _ (measurable_coordinateMarkPath n) measurable_id,
    marked_path_law n b hb μ]

end InvariantIsing

end

end OAI
