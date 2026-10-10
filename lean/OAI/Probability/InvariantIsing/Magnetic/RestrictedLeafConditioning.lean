import OAI.Probability.InvariantIsing.Magnetic.RestrictedPriorIntegrability
import OAI.Probability.InvariantIsing.Magnetic.RestrictedEndpointTest
import OAI.Probability.InvariantIsing.Fields.VectorTransitionShift

namespace OAI

/-! Exact conditioning of two constrained spins on their marked leaves.
The finite-prior normalization cancels from the leaf Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma referenceReplicaMean_add_constant {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (F : X → ℝ) (hF : Integrable (fun x => Real.exp (F x)) ν) (c : ℝ)
    {r : ℕ} (D : (Fin r → X) → ℝ) :
    referenceReplicaMean ν (fun x => F x + c) D = referenceReplicaMean ν F D := by
  have hi : Integrable (fun x => Real.exp (F x + c)) ν := by
    simpa only [Real.exp_add] using hF.mul_const (Real.exp c)
  rw [referenceReplicaMean_eq_tilted ν _ hi, referenceReplicaMean_eq_tilted ν _ hF,
    tilted_add_constant ν F hF c]

lemma restricted_two_gibbs_coordinate_mean {N : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (z : Fin 2 → Fin N → ℝ) (j : Fin N) :
    (∫ σ : Fin 2 → Spin N, spinValue (σ 0 j) * spinValue (σ 1 j)
      ∂Measure.pi (fun i => gibbsProbability (restrictedSpinPrior S hS : Measure (Spin N))
        (fieldEnergy (z i)))) = restrictedTerminalPairMean S j (z 0, z 1) := by
  let μ := fun i : Fin 2 => gibbsProbability (restrictedSpinPrior S hS : Measure (Spin N))
    (fieldEnergy (z i))
  have hm : Measurable (fun p : Spin N × Spin N => spinValue (p.1 j) * spinValue (p.2 j)) :=
    measurable_of_finite _
  have hp := (measurePreserving_piFinTwo μ).hasLaw.integral_comp hm.aestronglyMeasurable
  simp only [Function.comp_apply, MeasurableEquiv.piFinTwo_apply] at hp
  change (∫ σ : Fin 2 → Spin N, spinValue (σ 0 j) * spinValue (σ 1 j) ∂Measure.pi μ) = _
  rw [hp]
  dsimp only [μ]
  simp_rw [gibbsProbability_restrictedSpinPrior]
  let _ := restrictedSpinKernel_markov S hS
  rw [restrictedTerminalPairMean, Kernel.parallelComp_apply]
  rfl

theorem restricted_leaf_spin_pair_conditioning {N n : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (ν : Measure (LabeledLeaf n)) [IsProbabilityMeasure ν]
    (Y : LabeledLeaf n → Fin N → ℝ)
    (he : Integrable (fun p : Spin N × LabeledLeaf n => Real.exp (fieldEnergy (Y p.2) p.1))
      ((restrictedSpinPrior S hS : Measure (Spin N)).prod ν))
    (ψ : ℕ → ℝ) {C : ℝ} (hψ : ∀ d, |ψ d| ≤ C) (j : Fin N) :
    referenceReplicaMean ((restrictedSpinPrior S hS : Measure (Spin N)).prod ν)
      (fun p => fieldEnergy (Y p.2) p.1)
      (fun σ : Fin 2 → Spin N × LabeledLeaf n =>
        ψ (labeledCommonDepth n (σ 0).2 (σ 1).2) *
          (spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j))) =
      referenceReplicaMean ν (fun α => restrictedFieldTerminal S (Y α))
        (fun α : Fin 2 → LabeledLeaf n => ψ (labeledCommonDepth n (α 0) (α 1)) *
          restrictedTerminalPairMean S j (Y (α 0), Y (α 1))) := by
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
  have hD : ∃ C : ℝ, ∀ σ : Fin 2 → Spin N × LabeledLeaf n,
      |ψ (labeledCommonDepth n (σ 0).2 (σ 1).2) *
        (spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j))| ≤ C := by
    refine ⟨C, fun σ => ?_⟩
    simpa only [abs_mul, abs_spinValue, one_mul, mul_one] using
      hψ (labeledCommonDepth n (σ 0).2 (σ 1).2)
  rw [priorSpinLeafPair_conditioning μ ν H he _ hD, ← ht,
    referenceReplicaMean_add_constant ν T hi c]
  congr 1
  funext α
  change (∫ σ : Fin 2 → Spin N,
    ψ (labeledCommonDepth n (α 0) (α 1)) * (spinValue (σ 0 j) * spinValue (σ 1 j))
    ∂Measure.pi (fun i => gibbsProbability μ (fieldEnergy (Y (α i))))) = _
  rw [integral_const_mul]
  exact congrArg (fun x => ψ (labeledCommonDepth n (α 0) (α 1)) * x)
    (restricted_two_gibbs_coordinate_mean S hS (fun i => Y (α i)) j)

end InvariantIsing

end

end OAI
