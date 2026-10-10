import OAI.Probability.InvariantIsing.Fields.FieldPublishedEvaluation
import OAI.Probability.InvariantIsing.Arrays.NSpinTensorPairConditioning

namespace OAI

/-! Physical spins conditional on the two scalar-field endpoints. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma field_two_gibbs_coordinate_mean {N : ℕ} (z : Fin 2 → Fin N → ℝ) (j : Fin N) :
    (∫ σ : Fin 2 → Spin N, spinValue (σ 0 j) * spinValue (σ 1 j)
      ∂Measure.pi (fun i => gibbsProbability (uniformSpinPrior N : Measure (Spin N))
        (fieldEnergy (z i)))) = Real.tanh (z 0 j) * Real.tanh (z 1 j) := by
  let μ := fun i : Fin 2 => gibbsProbability (uniformSpinPrior N : Measure (Spin N))
    (fieldEnergy (z i))
  have hm : Measurable (fun p : Spin N × Spin N => spinValue (p.1 j) * spinValue (p.2 j)) :=
    measurable_of_finite _
  have hp := (measurePreserving_piFinTwo μ).hasLaw.integral_comp hm.aestronglyMeasurable
  simp only [Function.comp_apply, MeasurableEquiv.piFinTwo_apply] at hp
  change (∫ σ : Fin 2 → Spin N, spinValue (σ 0 j) * spinValue (σ 1 j) ∂Measure.pi μ) = _
  rw [hp, integral_prod_mul (fun σ : Spin N => spinValue (σ j))
    (fun σ : Spin N => spinValue (σ j))]
  exact congrArg₂ (fun a b : ℝ => a * b)
    (fieldSpinGibbs_coordinate_mean (z 0) j) (fieldSpinGibbs_coordinate_mean (z 1) j)

theorem field_leaf_spin_pair_conditioning {N n : ℕ}
    (ν : Measure (LabeledLeaf n)) [IsProbabilityMeasure ν]
    (Y : LabeledLeaf n → Fin N → ℝ)
    (he : Integrable (fun p : Spin N × LabeledLeaf n => Real.exp (fieldEnergy (Y p.2) p.1))
      ((uniformSpinPrior N : Measure (Spin N)).prod ν))
    (ψ : ℕ → ℝ) {C : ℝ} (hψ : ∀ d, |ψ d| ≤ C) (j : Fin N) :
    referenceReplicaMean ((uniformSpinPrior N : Measure (Spin N)).prod ν)
      (fun p => fieldEnergy (Y p.2) p.1)
      (fun σ : Fin 2 → Spin N × LabeledLeaf n =>
        ψ (labeledCommonDepth n (σ 0).2 (σ 1).2) *
          (spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j))) =
      referenceReplicaMean ν (fun α => ∑ i, Real.log (Real.cosh (Y α i)))
        (fun α : Fin 2 → LabeledLeaf n => ψ (labeledCommonDepth n (α 0) (α 1)) *
          (Real.tanh (Y (α 0) j) * Real.tanh (Y (α 1) j))) := by
  let H := fun p : Spin N × LabeledLeaf n => fieldEnergy (Y p.2) p.1
  have ht : spinLeafTerminal H = (fun α => ∑ i, Real.log (Real.cosh (Y α i))) := by
    funext α
    change finiteLogIntegral (uniformSpinPrior N : Measure (Spin N)) (fieldEnergy (Y α)) = _
    rw [finiteLogIntegral_uniformSpinPrior, logPartition_fieldEnergy]
  have hb : ∃ C : ℝ, ∀ σ : Fin 2 → Spin N × LabeledLeaf n,
      |ψ (labeledCommonDepth n (σ 0).2 (σ 1).2) *
        (spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j))| ≤ C := by
    refine ⟨C, fun σ => ?_⟩
    simpa only [abs_mul, abs_spinValue, one_mul, mul_one] using
      hψ (labeledCommonDepth n (σ 0).2 (σ 1).2)
  rw [spinLeafPair_conditioning ν H he _ hb, ht]
  congr 1
  funext α
  change (∫ σ : Fin 2 → Spin N,
    ψ (labeledCommonDepth n (α 0) (α 1)) * (spinValue (σ 0 j) * spinValue (σ 1 j))
    ∂Measure.pi (fun i => gibbsProbability (uniformSpinPrior N : Measure (Spin N))
      (fieldEnergy (Y (α i))))) = _
  rw [integral_const_mul, field_two_gibbs_coordinate_mean]

end InvariantIsing

end

end OAI
