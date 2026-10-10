import OAI.Probability.InvariantIsing.Fields.FieldSpinMeasurability

namespace OAI

/-! Preservation of the common-level law by the published finite-field
terminal tilt, including the independent scalar-field spins. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma field_leaf_depth_pair_conditioning {N n : ℕ}
    (ν : Measure (LabeledLeaf n)) [IsProbabilityMeasure ν]
    (Y : LabeledLeaf n → Fin N → ℝ)
    (he : Integrable (fun p : Spin N × LabeledLeaf n => Real.exp (fieldEnergy (Y p.2) p.1))
      ((uniformSpinPrior N : Measure (Spin N)).prod ν))
    (ψ : ℕ → ℝ) {C : ℝ} (hψ : ∀ d, |ψ d| ≤ C) :
    referenceReplicaMean ((uniformSpinPrior N : Measure (Spin N)).prod ν)
      (fun p => fieldEnergy (Y p.2) p.1)
      (fun σ : Fin 2 → Spin N × LabeledLeaf n => ψ (labeledCommonDepth n (σ 0).2 (σ 1).2)) =
      referenceReplicaMean ν (fun α => ∑ i, Real.log (Real.cosh (Y α i)))
        (fun α : Fin 2 → LabeledLeaf n => ψ (labeledCommonDepth n (α 0) (α 1))) := by
  let H := fun p : Spin N × LabeledLeaf n => fieldEnergy (Y p.2) p.1
  have ht : spinLeafTerminal H = (fun α => ∑ i, Real.log (Real.cosh (Y α i))) := by
    funext α
    change finiteLogIntegral (uniformSpinPrior N : Measure (Spin N)) (fieldEnergy (Y α)) = _
    rw [finiteLogIntegral_uniformSpinPrior, logPartition_fieldEnergy]
  rw [spinLeafPair_conditioning ν H he _ ⟨C, fun σ => hψ _⟩, ht]
  congr 1
  funext α
  change (∫ _ : Fin 2 → Spin N, ψ (labeledCommonDepth n (α 0) (α 1)) ∂_) = _
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

lemma field_published_depth_test (hpub : PanchenkoTalagrandFieldPairInput)
    (N : ℕ) (hN : 0 < N) (h : FieldStep) (ψ : ℕ → ℝ)
    {C : ℝ} (hψ : ∀ d, |ψ d| ≤ C) (z : Fin N → ℝ) :
    fieldVectorTiltedPairMean N h z (fun p => ψ p.1) =
      ∫ s, ψ (fieldLevelIndex h s).val ∂pathMeasure := by
  have hm : Measurable (fun p : ℕ × ((Fin N → ℝ) × (Fin N → ℝ)) => ψ p.1) :=
    (measurable_of_countable ψ).comp measurable_fst
  rw [hpub N hN h z (fun p => ψ p.1) hm ⟨C, fun p => hψ p.1⟩]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  exact fieldCommonLevel_integral h (fun i => ψ i.val)

def fieldDepthPairIntegrand (N : ℕ) (h : FieldStep) (z : Fin N → ℝ)
    (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) (ψ : ℕ → ℝ) : ℝ :=
  referenceReplicaMean
    ((uniformSpinPrior N : Measure (Spin N)).prod (labeledLeafLaw h.depth p.1))
    (fun s : Spin N × LabeledLeaf h.depth => fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1)
    (fun σ : Fin 2 → Spin N × LabeledLeaf h.depth =>
      ψ (labeledCommonDepth h.depth (σ 0).2 (σ 1).2))

def fieldVectorDepthPairMean (N : ℕ) (h : FieldStep) (z : Fin N → ℝ) (ψ : ℕ → ℝ) : ℝ :=
  ∫ p, fieldDepthPairIntegrand N h z p ψ ∂fieldVectorCoordinateLaw N h

lemma measurable_fieldDepthPairIntegrand (N : ℕ) (h : FieldStep) (ψ : ℕ → ℝ) :
    Measurable (fun p : (Fin N → ℝ) ×
      (LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) =>
        fieldDepthPairIntegrand N h p.1 p.2 ψ) := by
  let D : (Fin 2 → Spin N × LabeledLeaf h.depth) → ℝ := fun σ =>
    ψ (labeledCommonDepth h.depth (σ 0).2 (σ 1).2)
  have hm := measurable_cascadeCoordinateReplicaMean h.depth
    (uniformSpinPrior N : Measure (Spin N)) (measurable_fieldEnergy_map N) D
  have hc : Measurable (fun p : (Fin N → ℝ) ×
      (LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) =>
        (p.1, fieldEnergyCoordinates N h p.2)) :=
    measurable_fst.prodMk ((measurable_fieldEnergyCoordinates N h).comp measurable_snd)
  have he (z : Fin N → ℝ)
      (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) :
      cascadeCoordinateEnergy h.depth (fieldEnergy z) (fieldEnergyCoordinates N h p) =
        fun s => fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1 :=
    funext (fieldEnergyCoordinates_energy N h p z)
  have hh := hm.comp hc
  simp only [Function.comp_def] at hh
  simp_rw [he] at hh
  simpa only [labeledSpinReference, fieldEnergyCoordinates, fieldDepthPairIntegrand, D] using hh

lemma measurable_fieldVectorDepthPairMean (N : ℕ) (h : FieldStep) (ψ : ℕ → ℝ) :
    Measurable (fun z => fieldVectorDepthPairMean N h z ψ) :=
  (measurable_fieldDepthPairIntegrand N h ψ).stronglyMeasurable.integral_prod_right'.measurable

theorem field_vector_depth_pair_evaluation (hpub : PanchenkoTalagrandFieldPairInput)
    (N : ℕ) (hN : 0 < N) (h : FieldStep) (ψ : ℕ → ℝ)
    {C : ℝ} (hψ : ∀ d, |ψ d| ≤ C) (z : Fin N → ℝ) :
    fieldVectorDepthPairMean N h z ψ = ∫ s, ψ (fieldLevelIndex h s).val ∂pathMeasure := by
  rw [← field_published_depth_test hpub N hN h ψ hψ z]
  unfold fieldVectorDepthPairMean fieldVectorTiltedPairMean
  apply integral_congr_ae
  filter_upwards [field_vector_spin_exp_integrable N hN h z] with p hp
  exact field_leaf_depth_pair_conditioning (labeledLeafLaw h.depth p.1)
    (fieldVectorEndpoint N h p z) hp ψ hψ

end InvariantIsing

end

end OAI
