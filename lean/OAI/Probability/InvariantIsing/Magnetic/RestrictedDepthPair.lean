import OAI.Probability.InvariantIsing.Magnetic.RestrictedSpinEvaluation
import OAI.Probability.InvariantIsing.Fields.FieldDepthPair

namespace OAI

/-! Preservation of the common-level law by the published finite-field
terminal tilt, including the independent scalar-field spins. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma restricted_leaf_depth_pair_conditioning {N n : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (ν : Measure (LabeledLeaf n)) [IsProbabilityMeasure ν]
    (Y : LabeledLeaf n → Fin N → ℝ)
    (he : Integrable (fun p : Spin N × LabeledLeaf n => Real.exp (fieldEnergy (Y p.2) p.1))
      ((restrictedSpinPrior S hS : Measure (Spin N)).prod ν))
    (ψ : ℕ → ℝ) {C : ℝ} (hψ : ∀ d, |ψ d| ≤ C) :
    referenceReplicaMean ((restrictedSpinPrior S hS : Measure (Spin N)).prod ν)
      (fun p => fieldEnergy (Y p.2) p.1)
      (fun σ : Fin 2 → Spin N × LabeledLeaf n => ψ (labeledCommonDepth n (σ 0).2 (σ 1).2)) =
      referenceReplicaMean ν (fun α => restrictedFieldTerminal S (Y α))
        (fun α : Fin 2 → LabeledLeaf n => ψ (labeledCommonDepth n (α 0) (α 1))) := by
  let μ : Measure (Spin N) := restrictedSpinPrior S hS
  let H := fun p : Spin N × LabeledLeaf n => fieldEnergy (Y p.2) p.1
  let T := priorSpinLeafTerminal μ H
  let c := Real.log S.card - N * Real.log 2
  have ht : (fun α => T α + c) = (fun α => restrictedFieldTerminal S (Y α)) := by
    funext α
    change finiteLogIntegral μ (fieldEnergy (Y α)) + c = _
    rw [show μ = (restrictedSpinPrior S hS : Measure (Spin N)) from rfl,
      finiteLogIntegral_restrictedSpinPrior]
    dsimp only [c, restrictedFieldTerminal]
    ring
  have hi := priorSpinLeafTerminal_exp_integrable μ ν H he
  rw [priorSpinLeafPair_conditioning μ ν H he _ ⟨C, fun σ => hψ _⟩]
  have hc := referenceReplicaMean_add_constant ν T hi c
    (fun α : Fin 2 → LabeledLeaf n => ψ (labeledCommonDepth n (α 0) (α 1)))
  rw [ht] at hc
  rw [hc]
  congr 1
  funext α
  change (∫ _ : Fin 2 → Spin N, ψ (labeledCommonDepth n (α 0) (α 1)) ∂_) = _
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

lemma restricted_published_depth_test (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) (hN : 0 < N) (h : FieldStep) (ψ : ℕ → ℝ)
    {C : ℝ} (hψ : ∀ d, |ψ d| ≤ C) (z : Fin N → ℝ) :
    restrictedFieldTiltedPairMean S h z (fun p => ψ p.1) =
      ∫ s, ψ (fieldLevelIndex h s).val ∂pathMeasure := by
  have hm : Measurable (fun p : ℕ × ((Fin N → ℝ) × (Fin N → ℝ)) => ψ p.1) :=
    (measurable_of_countable ψ).comp measurable_fst
  rw [hpub N hN S hS h z (fun p => ψ p.1) hm ⟨C, fun p => hψ p.1⟩]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  exact fieldCommonLevel_integral h (fun i => ψ i.val)

def restrictedFieldDepthPairIntegrand {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (z : Fin N → ℝ)
    (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) (ψ : ℕ → ℝ) : ℝ :=
  referenceReplicaMean
    ((restrictedSpinPrior S hS : Measure (Spin N)).prod (labeledLeafLaw h.depth p.1))
    (fun s : Spin N × LabeledLeaf h.depth => fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1)
    (fun σ : Fin 2 → Spin N × LabeledLeaf h.depth =>
      ψ (labeledCommonDepth h.depth (σ 0).2 (σ 1).2))

def restrictedFieldDepthPairMean {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (z : Fin N → ℝ) (ψ : ℕ → ℝ) : ℝ :=
  ∫ p, restrictedFieldDepthPairIntegrand S hS h z p ψ ∂fieldVectorCoordinateLaw N h

lemma measurable_restrictedFieldDepthPairIntegrand {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (ψ : ℕ → ℝ) :
    Measurable (fun p : (Fin N → ℝ) ×
      (LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) =>
        restrictedFieldDepthPairIntegrand S hS h p.1 p.2 ψ) := by
  let D : (Fin 2 → Spin N × LabeledLeaf h.depth) → ℝ := fun σ =>
    ψ (labeledCommonDepth h.depth (σ 0).2 (σ 1).2)
  have hm := measurable_cascadeCoordinateReplicaMean h.depth
    (restrictedSpinPrior S hS : Measure (Spin N)) (measurable_fieldEnergy_map N) D
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
  simpa only [labeledSpinReference, fieldEnergyCoordinates, restrictedFieldDepthPairIntegrand, D] using hh

lemma measurable_restrictedFieldDepthPairMean {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (ψ : ℕ → ℝ) :
    Measurable (fun z => restrictedFieldDepthPairMean S hS h z ψ) :=
  (measurable_restrictedFieldDepthPairIntegrand S hS h ψ).stronglyMeasurable.integral_prod_right'.measurable

theorem restricted_field_depth_pair_evaluation (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) (hN : 0 < N) (h : FieldStep) (ψ : ℕ → ℝ)
    {C : ℝ} (hψ : ∀ d, |ψ d| ≤ C) (z : Fin N → ℝ) :
    restrictedFieldDepthPairMean S hS h z ψ = ∫ s, ψ (fieldLevelIndex h s).val ∂pathMeasure := by
  rw [← restricted_published_depth_test hpub S hS hN h ψ hψ z]
  unfold restrictedFieldDepthPairMean restrictedFieldTiltedPairMean
  apply integral_congr_ae
  filter_upwards [restricted_field_vector_spin_exp_integrable hN S hS h z] with p hp
  exact restricted_leaf_depth_pair_conditioning S hS (labeledLeafLaw h.depth p.1)
    (fieldVectorEndpoint N h p z) hp ψ hψ

end InvariantIsing

end

end OAI
