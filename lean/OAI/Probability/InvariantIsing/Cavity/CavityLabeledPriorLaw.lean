import OAI.Probability.InvariantIsing.Cavity.CavityPriorEndpointLaw

namespace OAI

/-! The full unweighted labeled cavity prior has a Gaussian endpoint law.
This controls its ordinary moments without assumptions on individual forests. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators ENNReal

namespace InvariantIsing

lemma cavity_prior_endpoint_mixture_lintegral {d : ℕ} (n : ℕ)
    (T : LabeledTree n) (ν : Measure (LabeledLeaf n)) [IsProbabilityMeasure ν]
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hS₀ : S₀.PosSemidef) (hR : R.PosSemidef) (hS : ∀ i, (S i).PosSemidef)
    (f : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ sg, ∫⁻ α, ∫⁻ z, f ((sg.1 + ∑ i : Fin n, sg.2 (edgeAt n α i)) + z)
      ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R ∂ν
      ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
        (Measure.infinitePi (fun v : ForestVertex n =>
          multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))) =
    ∫⁻ y, f y ∂multivariateGaussian 0 ((S₀ + ∑ i : Fin n, S i) + R) := by
  let PS := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
    (Measure.infinitePi (fun v : ForestVertex n =>
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))
  have hm : Measurable (fun p :
      (EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) ×
        (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) =>
      f ((p.1.1 + ∑ i : Fin n, p.1.2 (edgeAt n p.2.1 i)) + p.2.2)) := by
    have he := (measurable_cavityLabeledEndpoint (d := d) (k := 0) n).fst.comp
      (show Measurable (fun p :
        (EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) ×
          (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) =>
        ((T, p.1), (p.2, (fun _ : Fin 0 => false)))) from by fun_prop)
    exact hf.comp he
  have hinner : Measurable (fun p :
      (EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) × LabeledLeaf n =>
      ∫⁻ z, f ((p.1.1 + ∑ i : Fin n, p.1.2 (edgeAt n p.2 i)) + z)
        ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R) := by
    have hmp : Measurable (fun p :
        ((EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) × LabeledLeaf n) ×
          EuclideanSpace ℝ (Fin d) =>
        f ((p.1.1.1 + ∑ i : Fin n, p.1.1.2 (edgeAt n p.1.2 i)) + p.2)) :=
      hm.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
    exact hmp.lintegral_prod_right'
  rw [lintegral_lintegral_swap hinner.aemeasurable]
  have he (α : LabeledLeaf n) :
      (∫⁻ sg, ∫⁻ z, f ((sg.1 + ∑ i : Fin n, sg.2 (edgeAt n α i)) + z)
        ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R ∂PS) =
      ∫⁻ y, f y ∂multivariateGaussian 0 ((S₀ + ∑ i : Fin n, S i) + R) := by
    have hmap := cavity_prior_endpoint_law n S₀ R S hS₀ hR hS α
    rw [← hmap, lintegral_map hf (by fun_prop)]
    have hmz : Measurable (fun z :
        (EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) ×
          EuclideanSpace ℝ (Fin d) =>
        f ((z.1.1 + ∑ i : Fin n, z.1.2 (edgeAt n α i)) + z.2)) :=
      hf.comp (by fun_prop)
    exact (lintegral_prod _ hmz.aemeasurable).symm
  calc
    _ = ∫⁻ _α, ∫⁻ y, f y ∂multivariateGaussian 0 ((S₀ + ∑ i : Fin n, S i) + R) ∂ν :=
      lintegral_congr (fun α => he α)
    _ = _ := by simp


theorem cavity_labeled_prior_endpoint_law {d k : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hS₀ : S₀.PosSemidef) (hR : R.PosSemidef) (hS : ∀ i, (S i).PosSemidef)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    ((cavityLabeledDisorderLaw n b S₀ S) ⊗ₘ (cavityLabeledPriorKernel n R π)).map
      (fun p => (cavityLabeledEndpoint n p).1) =
    multivariateGaussian 0 ((S₀ + ∑ i : Fin n, S i) + R) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hm : Measurable (fun p : CavityLabeledDisorder d n × CavityLabeledState d k n =>
      f ((cavityLabeledEndpoint n p).1)) :=
    hf.comp (measurable_cavityLabeledEndpoint (d := d) (k := k) n).fst
  rw [lintegral_map hf (measurable_cavityLabeledEndpoint (d := d) (k := k) n).fst,
    Measure.lintegral_compProd hm]
  have hinner (T : LabeledTree n) :
      (∫⁻ sg, ∫⁻ x, f ((cavityLabeledEndpoint n ((T, sg), x)).1)
        ∂cavityLabeledPriorKernel n R π (T, sg)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
          (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))) =
      ∫⁻ y, f y ∂multivariateGaussian 0 ((S₀ + ∑ i : Fin n, S i) + R) := by
    have hx (sg : EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) :
        Measurable (fun x : CavityLabeledState d k n =>
          f ((cavityLabeledEndpoint n ((T, sg), x)).1)) :=
      hm.comp (measurable_const.prodMk measurable_id)
    have he sg :
        (∫⁻ x, f ((cavityLabeledEndpoint n ((T, sg), x)).1)
          ∂cavityLabeledPriorKernel n R π (T, sg)) =
        ∫⁻ α, ∫⁻ z, f ((sg.1 + ∑ i : Fin n, sg.2 (edgeAt n α i)) + z)
          ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R ∂labeledLeafLaw n T := by
      rw [cavityLabeledPriorKernel_apply, lintegral_prod _ (hx sg).aemeasurable]
      simp only [cavityLabeledEndpoint, cavityLabeledField, lintegral_const,
        measure_univ, mul_one]
      rw [lintegral_prod _]
      exact (hf.comp ((measurable_cavityLabeledEndpoint (d := d) (k := 0) n).fst.comp
        (show Measurable (fun p : LabeledLeaf n × EuclideanSpace ℝ (Fin d) =>
          ((T, sg), (p, (fun _ : Fin 0 => false)))) from by fun_prop))).aemeasurable
    simp_rw [he]
    exact cavity_prior_endpoint_mixture_lintegral n T (labeledLeafLaw n T)
      S₀ R S hS₀ hR hS f hf
  unfold cavityLabeledDisorderLaw
  rw [lintegral_prod _]
  · simp_rw [hinner]
    simp
  · exact (hm.lintegral_kernel_prod_right' (κ := cavityLabeledPriorKernel n R π)).aemeasurable

end InvariantIsing

end

end OAI
