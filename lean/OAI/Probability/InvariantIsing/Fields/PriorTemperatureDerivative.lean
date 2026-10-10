import OAI.Probability.InvariantIsing.Fields.PriorTemperatureCGF
import OAI.Probability.InvariantIsing.Pressure.ThermalPressure

namespace OAI

/-! Differentiation of the actual fixed-prior mean pressure. The derivative
is the original interaction energy, with both perturbations held fixed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology
namespace InvariantIsing

theorem hasDerivAt_priorPerturbationPressureMean_temperature
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (v : Fin m → ℝ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (K : ℝ) (hK : ∀ i, |eig i| ≤ K) (t : ℝ) :
    HasDerivAt (fun s => priorPerturbationPressureMean μ ν eig c I s h u v)
      (priorNamespacedObservableAverage μ ν (diagonalPerturbedEigenvalues eig I v t) c I
        (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
        (fun j : Fin N => enumeratedTreeDegree m j) h
        (fun U x => (N : ℝ)⁻¹*rotatedEnergy eig (specialRotation U) x.1)) t := by
  let d := fun j : Fin N => enumeratedSpectralDegree m j
  let r := fun j : Fin N => enumeratedTreeDegree m j
  let q := fun i : Fin (n+1) => tensorPathProfile I d n r h i
  let P := μ.prod gaussianCoordinates
  let G := priorNamespacedReference ν (diagonalPerturbedEigenvalues eig I v 0)
    c I d (tensorPerturbationAmplitude N u) q
  let Y := fun (p : SpecialOrthogonal N × (ℕ → ℝ)) (x : Spin N × LabeledLeaf n) =>
    rotatedEnergy eig (specialRotation p.1) x.1
  have hY : Measurable (Function.uncurry Y) := measurable_priorTemperatureObservable eig
  have hB p x : |Y p x| ≤ K*N/2 := abs_rotatedEnergy_le eig (specialRotation p.1) K hK x.1
  have hd := hasDerivAt_bounded_random_cgf P G
    (measurable_priorNamespacedReference ν _ c I d _ q) Y hY (K*N/2) hB t
  let M := fun s => priorPerturbationPressureMean μ ν eig c I s h u v
  have hi s : Integrable (priorNamespacedLog ν (diagonalPerturbedEigenvalues eig I v s)
      c I d (tensorPerturbationAmplitude N u) q) P :=
    priorNamespacedLog_integrable hhaar hgauss hN μ hμ ν _ c I d _
      (fun i => varianceIncrement h i) (fun i j => varianceIncrement (monomialPath n (r j)) i)
  have he s : M s = M 0+(∫ p, cgf (Y p) (G p) s ∂P)/N := by
    rw [integral_congr_ae (priorTemperatureCGF_eq_log_difference (by omega) μ ν eig c I v
      d (tensorPerturbationAmplitude N u) r h hh h0 s), integral_sub (hi s) (hi 0)]
    dsimp only [P]
    rw [priorNamespacedLog_integral, priorNamespacedLog_integral]
    dsimp only [M, priorPerturbationPressureMean, q, d, r]
    ring
  have hfold : (∫ p, ∫ x, Y p x ∂(G p).tilted (fun x => t*Y p x) ∂P) =
      ∫ p, ∫ x, Y p x ∂priorNamespacedReference ν
        (diagonalPerturbedEigenvalues eig I v t) c I d (tensorPerturbationAmplitude N u) q p ∂P := by
    apply integral_congr_ae
    filter_upwards [priorTemperature_reference_fold (by omega) μ ν eig c I v
      d (tensorPerturbationAmplitude N u) r h hh h0 t] with p hp
    rw [hp]
  have hf : M = fun s => M 0+(∫ p, cgf (Y p) (G p) s ∂P)/N := funext he
  have hD := (hd.div_const (N : ℝ)).const_add (M 0)
  rw [hfold, ← hf] at hD
  simpa only [M, Y, P, d, r, q, priorNamespacedObservableAverage, integral_const_mul,
    integral_mul_const, div_eq_mul_inv, mul_comm] using hD

end InvariantIsing

end

end OAI
