import OAI.Probability.InvariantIsing.Fields.FieldEndpointSampling
import OAI.Probability.InvariantIsing.Arrays.NSpinTensorAncestorInput

namespace OAI

/-!
The finite vector log-cosh specialization of Panchenko--Talagrand,
C. R. Acad. Sci. Paris I 345 (2007), 653--656, Section 3, Lemma 3.1,
equation (8), p.655, and Corollary 3.2, equation (9), p.656.

Only bounded measurable tests of the common depth and two endpoint fields
are retained. The statement specifies their law under the actual terminal
tilt, before any spins or overlap expectations are evaluated. The finite
marking theorem supplies this hypothesis.
-/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def fieldStepVariance (h : FieldStep) (i : ℕ) : ℝ≥0 :=
  if hi : i < h.depth then
    ((scalarFieldIncrements h).get ⟨i, by simpa only [scalarFieldIncrements_length] using hi⟩).2
  else 0

def fieldVectorCoordinateLaw (N : ℕ) (h : FieldStep) :
    Measure (LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) :=
  (labeledCascadeLaw h.depth (chainExponent h.cut) : Measure (LabeledTree h.depth)).prod
    (Measure.infinitePi (fun a : ForestVertex h.depth =>
      (vectorGaussianLaw N (fieldStepVariance h (forestVertexDepth h.depth a)) :
        Measure (Fin N → ℝ))))

def fieldVectorEndpoint (N : ℕ) (h : FieldStep)
    (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ))
    (z : Fin N → ℝ) (α : LabeledLeaf h.depth) : Fin N → ℝ :=
  labeledEnergy h.depth (markForestOfCoords _ h.depth p.2) α z

def fieldVectorTiltedPairMean (N : ℕ) (h : FieldStep) (z : Fin N → ℝ)
    (Φ : ℕ × ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ) : ℝ :=
  ∫ p, referenceReplicaMean (labeledLeafLaw h.depth p.1)
    (fun α => ∑ j, Real.log (Real.cosh (fieldVectorEndpoint N h p z α j)))
    (fun σ : Fin 2 → LabeledLeaf h.depth =>
      Φ (labeledCommonDepth h.depth (σ 0) (σ 1),
        fieldVectorEndpoint N h p z (σ 0), fieldVectorEndpoint N h p z (σ 1)))
    ∂fieldVectorCoordinateLaw N h

def FieldVectorAncestorPairLaw (N : ℕ) (h : FieldStep) : Prop :=
  ∀ z : Fin N → ℝ,
  ∀ Φ : ℕ × ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ,
    Measurable Φ → (∃ C : ℝ, ∀ p, |Φ p| ≤ C) →
    fieldVectorTiltedPairMean N h z Φ =
      ∫ α : ℕ → LabeledLeaf h.depth,
        ∫ y, Φ ((fieldCommonLevel h α).val, y)
          ∂fieldVectorPairEndpointKernel N (scalarFieldIncrements h)
            (scalarFieldIncrements_positive h)
            (Fin.cast (by rw [scalarFieldIncrements_length]) (fieldCommonLevel h α)) z
        ∂cascadeReplicaLaw h.depth (chainExponent h.cut)

/-- Same published marking result as `PanchenkoTalagrandTensorPairInput`,
specialized to the separable vector terminal used after the cavity change
of variables. No pressure, spin-moment, or limiting assertion is assumed. -/
def PanchenkoTalagrandFieldPairInput : Prop :=
  ∀ N : ℕ, 0 < N → ∀ h : FieldStep, FieldVectorAncestorPairLaw N h

lemma fieldVectorTerminal_linearGrowth (N : ℕ) :
    HasLinearGrowth (fun z : Fin N → ℝ => ∑ j, Real.log (Real.cosh (z j))) := by
  refine ⟨0, N, le_rfl, Nat.cast_nonneg _, ?_⟩
  intro z
  simp only [zero_add]
  calc
    _ ≤ ∑ j, |Real.log (Real.cosh (z j))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin N, ‖z‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact (abs_log_cosh_le (z j)).trans (by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm z j)
    _ = _ := by simp

/-- The actual terminal meets the published theorem's exponential moment
condition on every finite Gaussian path, including degenerate increments. -/
theorem fieldVectorFinitePath_exp_integrable (N : ℕ) (hN : 0 < N)
    (n : ℕ) (v : ℕ → ℝ≥0) (z : Fin N → ℝ) :
    Integrable (fun w : Fin n → Fin N → ℝ =>
      Real.exp (∑ j, Real.log (Real.cosh ((z + ∑ i, w i) j))))
      (Measure.pi (fun i : Fin n => (vectorGaussianLaw N (v i) : Measure (Fin N → ℝ)))) := by
  obtain ⟨C, L, _, hL, hbound⟩ := fieldVectorTerminal_linearGrowth N
  have hprod : Integrable (fun w : Fin n → Fin N → ℝ => ∏ i, Real.exp (L * ‖w i‖))
      (Measure.pi (fun i : Fin n => (vectorGaussianLaw N (v i) : Measure (Fin N → ℝ)))) :=
    Integrable.fintype_prod (f := fun (_i : Fin n) (a : Fin N → ℝ) => Real.exp (L * ‖a‖))
      fun i => vectorGaussianLaw_moments hN (v i) L
  have hm : Measurable (fun w : Fin n → Fin N → ℝ =>
      Real.exp (∑ j, Real.log (Real.cosh ((z + ∑ i, w i) j)))) := by
    apply Measurable.exp
    apply Finset.measurable_sum
    intro j _
    apply measurable_logCosh.comp
    exact (measurable_pi_apply j).comp
      (measurable_const.add (Finset.measurable_sum _ fun i _ => measurable_pi_apply i))
  apply (hprod.const_mul (Real.exp (C + L * ‖z‖))).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro w
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_sum, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ |∑ j, Real.log (Real.cosh ((z + ∑ i, w i) j))| := le_abs_self _
    _ ≤ C + L * ‖z + ∑ i, w i‖ := hbound _
    _ ≤ C + L * (‖z‖ + ∑ i, ‖w i‖) := by
      apply add_le_add_right (mul_le_mul_of_nonneg_left _ hL)
      exact (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ = C + L * ‖z‖ + ∑ i, L * ‖w i‖ := by rw [mul_add, Finset.mul_sum]; ring

end InvariantIsing

end

end OAI
