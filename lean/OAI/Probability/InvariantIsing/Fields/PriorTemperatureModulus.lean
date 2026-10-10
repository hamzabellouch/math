import OAI.Probability.InvariantIsing.Fields.PriorTensorMinimum
import OAI.Probability.InvariantIsing.Pressure.ThermalPressure

namespace OAI

/-! Temperature continuity for the actual fixed-prior pressure. The
spectral perturbation is held fixed while the original interaction scales. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

theorem priorPerturbationPressureMean_temperature_modulus
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (v : Fin m → ℝ) (K : ℝ) (hK : ∀ i, |eig i| ≤ K) (s t : ℝ) :
    |priorPerturbationPressureMean μ ν eig c I s h u v-
      priorPerturbationPressureMean μ ν eig c I t h u v| ≤ (K/2)*|s-t| := by
  let d := fun j : Fin N => enumeratedSpectralDegree m j
  let r := fun j : Fin N => enumeratedTreeDegree m j
  let q := fun i : Fin (n+1) => tensorPathProfile I d n r h i
  let F := fun t => priorTensorLog ν (diagonalPerturbedEigenvalues eig I v t) c I d
    (tensorPerturbationAmplitude N u) q
  have hi a : Integrable (F a) (μ.prod gaussianCoordinates) :=
    priorTensorLog_integrable hhaar hgauss hN μ hμ ν _ c I d _
      (fun i => varianceIncrement h i) (fun i j => varianceIncrement (monomialPath n (r j)) i)
  have hb (U : SpecialOrthogonal N) (x : Spin N × LabeledLeaf n) : |(rotatedEnergy (diagonalPerturbedEigenvalues eig I v s) (specialRotation U) x.1+
        fieldEnergy c x.1)-
      (rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) (specialRotation U) x.1+
        fieldEnergy c x.1)| ≤ |s-t| *(K*N/2) := by
    rw [add_sub_add_right_eq_sub, rotatedEnergy_diagonalPerturbation (by omega),
      rotatedEnergy_diagonalPerturbation (by omega)]
    rw [show s*rotatedEnergy eig (specialRotation U) x.1+
        (N : ℝ)*perturbationScale N*∑ a, v a*projectedOverlap (specialRotation U) (I a) x.1 x.1-
        (t*rotatedEnergy eig (specialRotation U) x.1+
        (N : ℝ)*perturbationScale N*∑ a, v a*projectedOverlap (specialRotation U) (I a) x.1 x.1) =
        (s-t)*rotatedEnergy eig (specialRotation U) x.1 by ring]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_rotatedEnergy_le eig (specialRotation U) K hK x.1) (abs_nonneg _)
  have hp U : |(∫ z, F s (U,z) ∂gaussianCoordinates)-
      ∫ z, F t (U,z) ∂gaussianCoordinates| ≤ |s-t| *(K*N/2) :=
    countable_cylinder_log_mean_base_compare ν
      (fun x => rotatedEnergy (diagonalPerturbedEigenvalues eig I v s) (specialRotation U) x.1+
        fieldEnergy c x.1)
      (fun x => rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) (specialRotation U) x.1+
        fieldEnergy c x.1)
      (finite_spin_base_exp_integrable ν (fun σ => rotatedEnergy (diagonalPerturbedEigenvalues eig I v s)
        (specialRotation U) σ+fieldEnergy c σ))
      (finite_spin_base_exp_integrable ν (fun σ => rotatedEnergy (diagonalPerturbedEigenvalues eig I v t)
        (specialRotation U) σ+fieldEnergy c σ))
      (tensorLeafCoefficients (specialRotation U) I d (tensorPerturbationAmplitude N u) n q)
      (tensorPathProfile_variance_cap (specialRotation U) I d (tensorPerturbationAmplitude N u)
        n r h hh h0) (hb U)
  unfold priorPerturbationPressureMean
  change |(N : ℝ)⁻¹*(∫ p, F s p ∂μ.prod gaussianCoordinates)-
    (N : ℝ)⁻¹*(∫ p, F t p ∂μ.prod gaussianCoordinates)| ≤ _
  rw [← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)),
    integral_prod _ (hi s), integral_prod _ (hi t),
    ← integral_sub (hi s).integral_prod_left (hi t).integral_prod_left]
  have ha := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun U => (∫ z, F s (U,z) ∂gaussianCoordinates)-∫ z, F t (U,z) ∂gaussianCoordinates)
    (ae_of_all _ fun U => by simpa only [Real.norm_eq_abs] using hp U)
  simp only [probReal_univ, mul_one, Real.norm_eq_abs] at ha
  refine (mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr (Nat.cast_nonneg N))).trans_eq ?_
  have hnz : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

end InvariantIsing

end

end OAI
