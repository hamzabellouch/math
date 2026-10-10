import OAI.Probability.InvariantIsing.Magnetic.RestrictedZeroTreeArrayLaw
import OAI.Probability.InvariantIsing.Magnetic.RestrictedOrientationLog
import OAI.Probability.InvariantIsing.Magnetic.RestrictedTreeLogMeasurability
import OAI.Probability.InvariantIsing.Fields.PriorTensorMinimum

namespace OAI

/-! Exact pressure transport from the constrained physical rotation to its
fixed-prior realization. Normalization is kept separate from the cube mass. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

lemma restricted_special_prior_log_mean {N m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (U : SpecialOrthogonal N)
    (T : LabeledTree depth) (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    (∫ z, priorTensorLog (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T)
      eig (fun _ => 0) I (fun j : Fin N => enumeratedSpectralDegree m j)
      (tensorPerturbationAmplitude N (fun j => u j))
      (fun i => tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j) depth
        (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0) i) (U,z) ∂gaussianCoordinates) =
      restrictedRotationLogMean S hS T eig I u ((cavitySpecialOrthogonal U)⁻¹) := by
  simp only [priorTensorLog, restrictedRotationLogMean, inv_inv,
    show matrixRotation (cavitySpecialOrthogonal U) = specialRotation U from rfl,
    cavityRotationHamiltonian, cavityPerturbationCoefficients,
    fieldEnergy, zero_mul, Finset.sum_const_zero, add_zero]

lemma restricted_prior_pressure_mean (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) {N m : ℕ} (hN : 3 ≤ N)
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (θ : Measure (LabeledTree 0)) [IsProbabilityMeasure θ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (hu : ∀ j, u j ∈ Set.Icc (1 : ℝ) 2)
    (v : Fin m → ℝ) (t : ℝ) :
    (N : ℝ) * priorPerturbationPressureMean
      (cavityOrientedBaseLaw (by omega) μ) (restrictedZeroTreePrior S hS)
      eig (fun _ => 0) I t (fun _ => 0) u v =
    ∫ p, restrictedRotationLogMean S hS p.2 (diagonalPerturbedEigenvalues eig I v t)
      I (cavityBaseAmplitude u) p.1 ∂μ.prod θ := by
  let E := diagonalPerturbedEigenvalues eig I v t
  let degree := fun j : Fin N => enumeratedSpectralDegree m j
  let profile : Fin (0+1) → SpinTensorIndex I degree → ℝ≥0 := fun i => tensorPathProfile I degree 0
    (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0) i
  let F := priorTensorLog (restrictedZeroTreePrior S hS) E (fun _ => 0) I degree
    (tensorPerturbationAmplitude N u) profile
  have hi : Integrable F ((cavityOrientedBaseLaw (by omega) μ).prod gaussianCoordinates) :=
    priorTensorLog_integrable hhaar hgauss hN _
      (cavityOrientedBaseLaw_leftInvariant (by omega) μ) _ E (fun _ => 0) I degree _
      (fun i => varianceIncrement (fun _ => 0) i)
      (fun i j => varianceIncrement (monomialPath 0 (enumeratedTreeDegree m j)) i)
  have hM : Measurable (fun U => ∫ z, F (U,z) ∂gaussianCoordinates) :=
    (measurable_priorTensorLog _ E (fun _ => 0) I degree _ profile).stronglyMeasurable
      |>.integral_prod_right' |>.measurable
  have he (U : SpecialOrthogonal N) : (∫ z, F (U,z) ∂gaussianCoordinates) =
      restrictedRotationLogMean (depth := 0) S hS (PUnit.unit : LabeledTree 0) E I (cavityBaseAmplitude u)
        ((cavitySpecialOrthogonal U)⁻¹) := by
    simpa only [F,profile,degree,restrictedZeroTreePrior,cavityBaseAmplitude_restrict] using
      restricted_special_prior_log_mean (depth := 0) S hS U (PUnit.unit : LabeledTree 0) E I (cavityBaseAmplitude u)
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold priorPerturbationPressureMean
  change (N : ℝ) * ((N : ℝ)⁻¹ * ∫ p, F p ∂_) = _
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul, integral_prod _ hi]
  rw [cavityOrientedBaseLaw]
  rw [integral_map (φ := fun V : Orthogonal N => cavityOrientationLift (by omega) V⁻¹)
    (((measurable_cavityOrientationLift (by omega)).comp measurable_inv).aemeasurable)
    hM.aestronglyMeasurable]
  simp_rw [he]
  have hor (V : Orthogonal N) := restricted_orientation_log_mean (depth := 0) (by omega) S hS V⁻¹
    (PUnit.unit : LabeledTree 0) E I (cavityBaseAmplitude u)
  simp only [inv_inv] at hor
  simp_rw [hor]
  symm
  have hiR := integrable_restrictedRotationLogMean_tree S hS μ θ E I (cavityBaseAmplitude u)
    (cavityBaseAmplitude_bound u hu)
  rw [integral_prod _ hiR]
  congr 1
  funext V
  have hT (T : LabeledTree 0) : T = (PUnit.unit : LabeledTree 0) := Subsingleton.elim _ _
  simp_rw [hT]
  simp only [integral_const, probReal_univ, one_smul]

end InvariantIsing

end

end OAI
