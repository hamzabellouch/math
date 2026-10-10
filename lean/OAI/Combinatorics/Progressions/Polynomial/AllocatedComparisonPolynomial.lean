import OAI.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedComparisonInitialLog {A : Type*} [Semiring A] (m : ℕ) (p : A) : A :=
  let D := allocatedComparisonDimension m p
  allocatedTestLengthEnvelope m D D D

noncomputable def allocatedComparisonScaleLog {A : Type*} [Semiring A] (m : ℕ) (p : A) : A :=
  let T := allocatedComparisonDimension m p+allocatedComparisonInitialLog m p+1
  (1+T^2)*(5*T+49)

theorem allocatedComparisonInitialLog_nonneg (m : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ allocatedComparisonInitialLog m p := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  exact allocatedTestLengthEnvelope_nonneg m hD hD hD

theorem allocatedComparisonScaleLog_nonneg (m : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ allocatedComparisonScaleLog m p := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hE := allocatedComparisonInitialLog_nonneg m hp
  dsimp only [allocatedComparisonScaleLog]
  positivity

theorem exists_allocatedComparisonScale_polynomial_bound (m A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      allocatedComparisonScaleLog m ((p+2)^A) ≤ (p+2)^C := by
  let P : Polynomial ℕ := allocatedComparisonScaleLog m ((Polynomial.X+2)^A)
  obtain ⟨C, hC, hb⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [P, allocatedComparisonScaleLog, allocatedComparisonInitialLog,
    allocatedComparisonDimension, allocatedTestLengthEnvelope, allocatedJointLengthEnvelope,
    allocatedFrontEnvelope, allocatedAccuracyEnvelope, allocatedTupleEnvelope,
    allocatedTestEnvelope, allocatedSupportEnvelope, allocatedDensityEnvelope,
    allocatedKernelEnvelope, kernelOutputEnvelope, kernelGeometryEnvelope,
    kernelInverseEnvelope, Polynomial.eval₂_pow] using hb p hp

noncomputable def allocatedComparisonExponent (m A : ℕ) : ℕ :=
  (exists_allocatedComparisonScale_polynomial_bound m A).choose

theorem allocatedComparisonExponent_two_le (m A : ℕ) : 2 ≤ allocatedComparisonExponent m A :=
  (exists_allocatedComparisonScale_polynomial_bound m A).choose_spec.1

theorem allocatedComparisonScaleLog_le_power (m A : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    allocatedComparisonScaleLog m ((p+2)^A) ≤ (p+2)^allocatedComparisonExponent m A :=
  (exists_allocatedComparisonScale_polynomial_bound m A).choose_spec.2 p hp

end Erdos3.VectorPolynomial

end

end OAI
