import OAI.Probability.InvariantIsing.Cavity.CavityProjectorHamiltonian

namespace OAI

/-! Measurable, bounded Gibbs observables expressed in the joint
projector and special-frame data. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

lemma measurable_cavityProjectorSpinCoordinate {N : ℕ} (σ : Spin N) (i : Fin N) :
    Measurable (fun Q : Matrix (Fin N) (Fin N) ℝ => cavityProjectorSpinCoordinate Q σ i) := by
  unfold cavityProjectorSpinCoordinate Matrix.mulVec dotProduct
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_pi_apply j).comp (measurable_pi_apply i)).mul_const _

lemma measurable_cavityProjectorMonomial {N m : ℕ} (degree : Fin m → ℕ)
    (σ : Spin N) (w : SpectralTensorIndex
      (fun _ : Fin m => (Finset.univ : Finset (Fin N))) degree) :
    Measurable (fun Q : Fin m → Matrix (Fin N) (Fin N) ℝ =>
      cavityProjectorMonomial Q degree σ w) := by
  unfold cavityProjectorMonomial tensorFeature
  apply Finset.measurable_prod
  intro a _
  apply Finset.measurable_prod
  intro j _
  exact (measurable_cavityProjectorSpinCoordinate σ (w a j)).comp (measurable_pi_apply a)

lemma measurable_cavityProjectorSpinFeature {N m : ℕ} (degree : Fin N → Fin m → ℕ)
    (amp : Fin N → ℝ) (σ : Spin N) (j : CavityProjectorTensorIndex N m degree) :
    Measurable (fun Q : Fin m → Matrix (Fin N) (Fin N) ℝ =>
      cavityProjectorSpinFeature Q degree amp σ j) := by
  cases j with
  | inl j => exact measurable_const
  | inr w => exact (measurable_cavityProjectorMonomial (degree w.1) σ w.2).const_mul _

lemma measurable_cavityProjectorField {N m depth : ℕ}
    (u : ℕ → ℝ) (x : Spin N × LabeledLeaf depth) :
    Measurable (fun p : (Fin m → Matrix (Fin N) (Fin N) ℝ) × (ℕ → ℝ) =>
      cylinderField (cavityProjectorPerturbation p.1 u x) p.2) := by
  simp only [cavityProjectorPerturbation, cylinderField_feature]
  apply Finset.measurable_sum
  intro i _
  exact (((measurable_cavityProjectorSpinFeature _ _ x.1 i.2).comp measurable_fst).const_mul _).mul
    ((measurable_pi_apply (treeFeatureTag depth x.2 i)).comp measurable_snd)

lemma measurable_cavityProjectorHamiltonian {N m depth : ℕ}
    (c : Fin m → ℝ) (u : ℕ → ℝ) :
    Measurable (fun p : ((Fin m → Matrix (Fin N) (Fin N) ℝ) × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf depth) => cavityProjectorHamiltonian p.1.1 c u p.1.2 p.2) := by
  apply measurable_from_prod_countable_left
  intro x
  have he : Measurable (fun Q : Fin m → Matrix (Fin N) (Fin N) ℝ =>
      cavityProjectorEnergy Q c x.1) := by
    unfold cavityProjectorEnergy Matrix.mulVec dotProduct
    fun_prop
  exact (he.comp measurable_fst).add (measurable_cavityProjectorField u x)

lemma measurable_cavityProjectorHamiltonian_pullback {Ω : Type*} [MeasurableSpace Ω]
    {N m depth : ℕ} (f : Ω → Fin m → Matrix (Fin N) (Fin N) ℝ) (hf : Measurable f)
    (c : Fin m → ℝ) (u : ℕ → ℝ) :
    Measurable (fun p : (Ω × (ℕ → ℝ)) × (Spin N × LabeledLeaf depth) =>
      cavityProjectorHamiltonian (f p.1.1) c u p.1.2 p.2) := by
  let π : (Ω × (ℕ → ℝ)) × (Spin N × LabeledLeaf depth) →
      ((Fin m → Matrix (Fin N) (Fin N) ℝ) × (ℕ → ℝ)) × (Spin N × LabeledLeaf depth) :=
    fun p => ((f p.1.1,p.1.2),p.2)
  have hπ : Measurable π :=
    ((hf.comp measurable_fst.fst).prodMk measurable_fst.snd).prodMk measurable_snd
  have hbase := measurable_cavityProjectorHamiltonian (N := N) (m := m) (depth := depth) c u
  have hcomp := hbase.comp hπ
  exact hcomp

def cavityProjectorReplicaMean {N m d depth r : ℕ} (T : LabeledTree depth)
    (c : Fin m → ℝ) (u : ℕ → ℝ)
    (F : CavityProjectorFrame N m d → (Fin r → Spin N × LabeledLeaf depth) → ℝ)
    (p : CavityProjectorFrame N m d) : ℝ :=
  ∫ z, referenceReplicaMean
    (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
    (cavityProjectorHamiltonian p.1 c u z) (F p) ∂gaussianCoordinates

lemma measurable_cavityProjectorReplicaMean {N m d depth r : ℕ} (T : LabeledTree depth)
    (c : Fin m → ℝ) (u : ℕ → ℝ)
    (F : CavityProjectorFrame N m d → (Fin r → Spin N × LabeledLeaf depth) → ℝ)
    (hF : Measurable (Function.uncurry F)) : Measurable (cavityProjectorReplicaMean T c u F) := by
  have hH := measurable_cavityProjectorHamiltonian_pullback
    (Prod.fst : CavityProjectorFrame N m d → Fin m → Matrix (Fin N) (Fin N) ℝ)
    measurable_fst c u (depth := depth)
  exact (measurable_referenceReplicaMean _ hH
    (hF.comp (measurable_fst.fst.prodMk measurable_snd))).stronglyMeasurable.integral_prod_right'.measurable

lemma cavityProjectorReplicaMean_bound {N m d depth r : ℕ} (T : LabeledTree depth)
    (c : Fin m → ℝ) (u : ℕ → ℝ)
    (F : CavityProjectorFrame N m d → (Fin r → Spin N × LabeledLeaf depth) → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hF : ∀ p σ, |F p σ| ≤ C) (p : CavityProjectorFrame N m d) :
    ‖cavityProjectorReplicaMean T c u F p‖ ≤ C := by
  have hb : ∀ᵐ z ∂gaussianCoordinates,
      ‖referenceReplicaMean (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
        (cavityProjectorHamiltonian p.1 c u z) (F p)‖ ≤ C :=
    ae_of_all _ fun z => by
      simpa only [Real.norm_eq_abs] using referenceReplicaMean_abs_le _ _ (F p)
        (measurable_of_countable _) hC (hF p)
  simpa only [cavityProjectorReplicaMean, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hb

end InvariantIsing

end

end OAI
