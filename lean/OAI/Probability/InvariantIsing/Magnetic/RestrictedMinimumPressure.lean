import OAI.Probability.InvariantIsing.Fields.PriorZeroFieldPressure

namespace OAI

/-! The minimizing constrained pressure envelope has exactly the physical
pressure limit, with its finite-volume cube-mass normalization restored. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology
namespace InvariantIsing

lemma restricted_zero_field_minimum_cost
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ)
    (u : Fin N → ℝ) (v : Fin m → ℝ)
    (hu : ∀ j, u j ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ a, v a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      priorPerturbationObjective μ (restrictedZeroTreePrior S hS) eig c I t (fun _ => 0) u v ≤
        priorPerturbationObjective μ (restrictedZeroTreePrior S hS) eig c I t (fun _ => 0) u' v') :
    |(-priorPerturbationObjective μ (restrictedZeroTreePrior S hS) eig c I t (fun _ => 0) u v +
      (N : ℝ)⁻¹*(Real.log S.card-N*Real.log 2)) -
      ∫ U, restrictedRotatedPressure S (fun i => t*eig i) (specialRotation U) c ∂μ| ≤
        2*m*perturbationScale N+8*perturbationScale N^2 ∧
    tensorMinimumPenalty u v ≤ 2*(2*m*perturbationScale N+8*perturbationScale N^2) := by
  have hc := prior_minimum_perturbation_cost hhaar hgauss hN μ hμ (restrictedZeroTreePrior S hS)
    eig c I t (fun _ => 0) monotone_const le_rfl u v hu hv hmin
  rw [restricted_zero_field_pressure] at hc
  constructor
  · convert hc.1 using 1
    congr 1
    ring
  · exact hc.2

lemma restricted_zero_field_minimum_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ r, 3 ≤ N r) (hNlim : Tendsto N atTop atTop) (m : ℕ)
    (μ : (r : ℕ) → Measure (SpecialOrthogonal (N r))) [∀ r, IsProbabilityMeasure (μ r)]
    (hμ : ∀ r, (μ r).IsMulLeftInvariant)
    (S : (r : ℕ) → Finset (Spin (N r))) (hS : ∀ r, (S r).Nonempty)
    (eig c : (r : ℕ) → Fin (N r) → ℝ) (I : (r : ℕ) → Fin m → Finset (Fin (N r)))
    (t : ℕ → ℝ) (u : (r : ℕ) → Fin (N r) → ℝ) (v : ℕ → Fin m → ℝ)
    (hu : ∀ r j, u r j ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ r a, v r a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ r u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      priorPerturbationObjective (μ r) (restrictedZeroTreePrior (S r) (hS r))
        (eig r) (c r) (I r) (t r) (fun _ => 0) (u r) (v r) ≤
      priorPerturbationObjective (μ r) (restrictedZeroTreePrior (S r) (hS r))
        (eig r) (c r) (I r) (t r) (fun _ => 0) u' v') :
    Tendsto (fun r => -priorPerturbationObjective (μ r) (restrictedZeroTreePrior (S r) (hS r))
      (eig r) (c r) (I r) (t r) (fun _ => 0) (u r) (v r) +
      (N r : ℝ)⁻¹*(Real.log (S r).card-N r*Real.log 2) -
      ∫ U, restrictedRotatedPressure (S r) (fun i => t r*eig r i) (specialRotation U) (c r) ∂μ r)
      atTop (𝓝 0) ∧
    Tendsto (fun r => tensorMinimumPenalty (u r) (v r)) atTop (𝓝 0) := by
  have hc r := restricted_zero_field_minimum_cost hhaar hgauss (hN r) (μ r) (hμ r)
    (S r) (hS r) (eig r) (c r) (I r) (t r) (u r) (v r) (hu r) (hv r) (hmin r)
  have hδ := (fullPerturbationCost_tendsto m).comp hNlim
  constructor
  · exact squeeze_zero_norm (fun r => by simpa only [Real.norm_eq_abs, Function.comp_def] using (hc r).1) hδ
  · apply squeeze_zero (fun r => tensorMinimumPenalty_nonneg (u r) (v r)) (fun r => (hc r).2)
    simpa only [mul_zero, Function.comp_def] using hδ.const_mul 2

end InvariantIsing

end

end OAI
