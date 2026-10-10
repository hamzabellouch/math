import OAI.Probability.InvariantIsing.Cavity.CavityGaussianCappedNumerator

namespace OAI

/-! The actual finite cavity model in a fixed measurable state space:
the tree, Gaussian root and forest are disorder; the leaf, ordinary
residual and Ising spin form the configuration. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

abbrev CavityLabeledDisorder (d n : ℕ) :=
  LabeledTree n × (EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d)))

abbrev CavityLabeledState (d k n : ℕ) :=
  (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) × Spin k

def cavityLabeledDisorderLaw {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ) :
    Measure (CavityLabeledDisorder d n) :=
  (labeledCascadeLaw n b : Measure (LabeledTree n)).prod
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
        (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v)))))

instance cavityLabeledDisorderLaw_probability {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ) :
    IsProbabilityMeasure (cavityLabeledDisorderLaw n b S₀ S) := by
  unfold cavityLabeledDisorderLaw
  infer_instance

def cavityLabeledLeafKernel (n : ℕ) : Kernel (LabeledTree n) (LabeledLeaf n) :=
  ⟨labeledLeafLaw n, measurable_labeledLeafLaw n⟩

instance cavityLabeledLeafKernel_markov (n : ℕ) : IsMarkovKernel (cavityLabeledLeafKernel n) :=
  ⟨fun T => inferInstanceAs (IsProbabilityMeasure (labeledLeafLaw n T))⟩

def cavityLabeledPriorKernel {d k : ℕ} (n : ℕ) (R : Matrix (Fin d) (Fin d) ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    Kernel (CavityLabeledDisorder d n) (CavityLabeledState d k n) :=
  (((cavityLabeledLeafKernel n).comap Prod.fst measurable_fst) ×ₖ
    Kernel.const _ (multivariateGaussian 0 R)) ×ₖ
    Kernel.const _ π

@[simp] lemma cavityLabeledPriorKernel_apply {d k : ℕ} (n : ℕ)
    (R : Matrix (Fin d) (Fin d) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (ω : CavityLabeledDisorder d n) :
    cavityLabeledPriorKernel n R π ω =
      (((labeledLeafLaw n ω.1).prod (multivariateGaussian 0 R)).prod π) := by
  rw [cavityLabeledPriorKernel, Kernel.prod_apply, Kernel.prod_apply]
  rfl

instance cavityLabeledPriorKernel_markov {d k : ℕ} (n : ℕ)
    (R : Matrix (Fin d) (Fin d) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    IsMarkovKernel (cavityLabeledPriorKernel n R π) := by
  constructor
  intro ω
  rw [cavityLabeledPriorKernel_apply]
  infer_instance

def cavityLabeledField {d : ℕ} (n : ℕ) (ω : CavityLabeledDisorder d n)
    (α : LabeledLeaf n) : EuclideanSpace ℝ (Fin d) :=
  ω.2.1 + ∑ i : Fin n, ω.2.2 (edgeAt n α i)

lemma measurable_cavityLabeledField {d : ℕ} (n : ℕ) :
    Measurable (fun p : CavityLabeledDisorder d n × LabeledLeaf n =>
      cavityLabeledField n p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro α
  change Measurable (fun ω : CavityLabeledDisorder d n =>
    ω.2.1 + ∑ i : Fin n, ω.2.2 (edgeAt n α i))
  exact measurable_snd.fst.add (Finset.measurable_sum _ fun i _ =>
    (measurable_pi_apply (edgeAt n α i)).comp measurable_snd.snd)

def cavityLabeledEndpoint {d k : ℕ} (n : ℕ)
    (p : CavityLabeledDisorder d n × CavityLabeledState d k n) :
    EuclideanSpace ℝ (Fin d) × Spin k :=
  (cavityLabeledField n p.1 p.2.1.1 + p.2.1.2, p.2.2)

lemma measurable_cavityLabeledEndpoint {d k : ℕ} (n : ℕ) :
    Measurable (cavityLabeledEndpoint (d := d) (k := k) n) := by
  have ha : Measurable (fun p : CavityLabeledDisorder d n × CavityLabeledState d k n =>
      (p.1, p.2.1.1)) := measurable_fst.prodMk measurable_snd.fst.fst
  have hf : Measurable (fun p : CavityLabeledDisorder d n × CavityLabeledState d k n =>
      cavityLabeledField n p.1 p.2.1.1) := (measurable_cavityLabeledField (d := d) n).comp ha
  have hr : Measurable (fun p : CavityLabeledDisorder d n × CavityLabeledState d k n =>
      p.2.1.2) := measurable_snd.fst.snd
  have hy : Measurable (fun p : CavityLabeledDisorder d n × CavityLabeledState d k n =>
      cavityLabeledField n p.1 p.2.1.1 + p.2.1.2) := hf.add hr
  have hs : Measurable (fun p : CavityLabeledDisorder d n × CavityLabeledState d k n =>
      p.2.2) := measurable_snd.snd
  exact hy.prodMk hs

def cavityLabeledPotential {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) : CavityLabeledDisorder d n × CavityLabeledState d k n → ℝ :=
  (fun p : EuclideanSpace ℝ (Fin d) × Spin k => cavityLogFactor K L C p.1 p.2) ∘
    cavityLabeledEndpoint n

lemma measurable_cavityLabeledPotential {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) : Measurable (cavityLabeledPotential n K L C) := by
  have hm : Measurable (fun p : EuclideanSpace ℝ (Fin d) × Spin k =>
      cavityLogFactor K L C p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro ε
    exact (continuous_cavityLogFactor K L C ε).measurable
  exact hm.comp (measurable_cavityLabeledEndpoint n)

end InvariantIsing

end

end OAI
