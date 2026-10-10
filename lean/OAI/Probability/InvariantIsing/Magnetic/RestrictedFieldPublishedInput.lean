import OAI.Probability.InvariantIsing.Magnetic.RestrictedEndpointKernel
import OAI.Probability.InvariantIsing.Fields.FieldPublishedPairInput

namespace OAI

/-! Panchenko--Talagrand (2007), Lemma 3.1 (8), p.655 and Corollary
3.2 (9), p.656, specialized to the actual finite constrained terminal.
The hypothesis concerns only the marked endpoint law; no pressure,
spin expectation, or limiting assertion is an input. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def restrictedFieldTiltedPairMean {N : ℕ} (S : Finset (Spin N))
    (h : FieldStep) (z : Fin N → ℝ)
    (Φ : ℕ × ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ) : ℝ :=
  ∫ p, referenceReplicaMean (labeledLeafLaw h.depth p.1)
    (fun α => restrictedFieldTerminal S (fieldVectorEndpoint N h p z α))
    (fun σ : Fin 2 → LabeledLeaf h.depth =>
      Φ (labeledCommonDepth h.depth (σ 0) (σ 1),
        fieldVectorEndpoint N h p z (σ 0), fieldVectorEndpoint N h p z (σ 1)))
    ∂fieldVectorCoordinateLaw N h

def RestrictedFieldAncestorPairLaw {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) : Prop :=
  ∀ z : Fin N → ℝ,
  ∀ Φ : ℕ × ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ,
    Measurable Φ → (∃ C : ℝ, ∀ p, |Φ p| ≤ C) →
    restrictedFieldTiltedPairMean S h z Φ =
      ∫ α : ℕ → LabeledLeaf h.depth,
        ∫ y, Φ ((fieldCommonLevel h α).val, y)
          ∂restrictedPairEndpointKernel hN S hS h.depth (chainExponent h.cut)
            (fieldStepVariance h)
            (fun i hi => ((chainExponent_admissible h.ordered_cut h.first h.last).1 i hi).1)
            (fieldCommonLevel h α) z
        ∂cascadeReplicaLaw h.depth (chainExponent h.cut)

/-- The same published marking theorem, with a nonempty finite spin
constraint retained inside the terminal log partition. -/
def PanchenkoTalagrandRestrictedFieldPairInput : Prop :=
  ∀ (N : ℕ) (hN : 0 < N) (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep),
    RestrictedFieldAncestorPairLaw hN S hS h

/-- The constrained terminal satisfies the published exponential-moment
condition on every finite Gaussian path, also for zero variances. -/
theorem restrictedFieldFinitePath_exp_integrable {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (n : ℕ) (v : ℕ → ℝ≥0) (z : Fin N → ℝ) :
    Integrable (fun w : Fin n → Fin N → ℝ =>
      Real.exp (restrictedFieldTerminal S (z + ∑ i, w i)))
      (Measure.pi (fun i : Fin n => (vectorGaussianLaw N (v i) : Measure (Fin N → ℝ)))) := by
  have hm : Measurable (fun w : Fin n → Fin N → ℝ =>
      Real.exp (restrictedFieldTerminal S (z + ∑ i, w i))) :=
    (((continuous_restrictedFieldTerminal S hS).measurable.comp
      (measurable_const.add (Finset.measurable_sum _ fun i _ => measurable_pi_apply i))).exp)
  apply (fieldVectorFinitePath_exp_integrable N hN n v z).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun w => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (restrictedFieldTerminal_le_univ S hS _))

end InvariantIsing

end

end OAI
