import OAI.Probability.InvariantIsing.Arrays.TensorMinimumPenalty
import OAI.Probability.InvariantIsing.Arrays.TensorZeroFieldPressure

namespace OAI

/-! Actual zero-field perturbation minima approximate the unperturbed Haar
pressure, with a uniform cost independent of the auxiliary cascade depth. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem tensor_zero_field_minimum_cost
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m : ℕ} (hN : 3≤N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (t : ℝ) (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (u : Fin N → ℝ) (v : Fin m → ℝ)
    (hu : ∀ j, u j ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ a, v a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective μ eig c I t n b (fun _ => 0) u v ≤
        tensorPerturbationObjective μ eig c I t n b (fun _ => 0) u' v') :
    |(-tensorPerturbationObjective μ eig c I t n b (fun _ => 0) u v) -
      ∫ U, rotatedPressure (fun i => t*eig i) (specialRotation U) c ∂μ| ≤
        2*m*perturbationScale N+8*perturbationScale N^2 ∧
    tensorMinimumPenalty u v ≤ 2*(2*m*perturbationScale N+8*perturbationScale N^2) := by
  apply tensor_minimum_envelope_cost μ eig c I t n b (fun _ => 0) u v hu hv hmin
  intro u' v' hu' hv'
  have hua : ∀ j, |u' j|≤2 := fun j => abs_le.mpr ⟨by linarith [(hu' j).1], (hu' j).2⟩
  have hva : ∀ a, |v' a|≤2 := fun a => abs_le.mpr ⟨by linarith [(hv' a).1], (hv' a).2⟩
  have hc := tensorNamespacedMeanPressure_zero_field_cost hhaar hgauss hN μ hμ eig c I
    u' hua v' hva t n b hb
  rw [tensorNamespacedMeanPressure_eq_perturbation μ eig c I u' v' t n b (fun _ => 0) hb] at hc
  simpa only [zero_div, sub_zero] using hc

/-- Both errors vanish along any diverging sequence of physical dimensions.
No fixed-depth assumption is required. -/
theorem tensor_zero_field_minimum_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ r, 3≤N r) (hNlim : Tendsto N atTop atTop) (m : ℕ)
    (μ : (r : ℕ) → Measure (SpecialOrthogonal (N r))) [∀ r, IsProbabilityMeasure (μ r)]
    (hμ : ∀ r, (μ r).IsMulLeftInvariant)
    (eig c : (r : ℕ) → Fin (N r) → ℝ) (I : (r : ℕ) → Fin m → Finset (Fin (N r)))
    (t : ℕ → ℝ) (n : ℕ → ℕ) (b : ℕ → ℕ → ℝ) (hb : ∀ r, CascadeExponents (n r) (b r))
    (u : (r : ℕ) → Fin (N r) → ℝ) (v : ℕ → Fin m → ℝ)
    (hu : ∀ r j, u r j ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ r a, v r a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ r u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective (μ r) (eig r) (c r) (I r) (t r) (n r) (b r) (fun _ => 0) (u r) (v r) ≤
        tensorPerturbationObjective (μ r) (eig r) (c r) (I r) (t r) (n r) (b r) (fun _ => 0) u' v') :
    Tendsto (fun r => -tensorPerturbationObjective (μ r) (eig r) (c r) (I r) (t r) (n r)
      (b r) (fun _ => 0) (u r) (v r) -
      ∫ U, rotatedPressure (fun i => t r*eig r i) (specialRotation U) (c r) ∂μ r) atTop (𝓝 0) ∧
    Tendsto (fun r => tensorMinimumPenalty (u r) (v r)) atTop (𝓝 0) := by
  have hc r := tensor_zero_field_minimum_cost hhaar hgauss (hN r) (μ r) (hμ r)
    (eig r) (c r) (I r) (t r) (n r) (b r) (hb r) (u r) (v r) (hu r) (hv r) (hmin r)
  have hδ := (fullPerturbationCost_tendsto m).comp hNlim
  constructor
  · exact squeeze_zero_norm (fun r => by simpa only [Real.norm_eq_abs, Function.comp_def] using (hc r).1) hδ
  · apply squeeze_zero (fun r => tensorMinimumPenalty_nonneg (u r) (v r))
      (fun r => (hc r).2)
    simpa only [mul_zero, Function.comp_def] using hδ.const_mul 2

end InvariantIsing

end

end OAI
