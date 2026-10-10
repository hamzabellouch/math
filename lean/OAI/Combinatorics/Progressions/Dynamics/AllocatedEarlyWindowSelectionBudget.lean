import OAI.Combinatorics.Progressions.Probability.AllocatedProbabilityWindowMesh

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedEarlyWindowSelectionLog {A : Type*} [Semiring A]
    (m dim : ℕ) (s : A) : A :=
  let D := allocatedComparisonDimension m s
  allocatedSiteFamilyWindowLog D + D * allocatedSiteKernelMaskLog m s + 1 +
    (coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim s) + s) + 1

theorem allocatedEarlyWindowSelection_denominator (m dim : ℕ) {p E P Q D s : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hP : 0 ≤ P) (hD : 0 ≤ D) (hs : 0 ≤ s)
    (hDs : D ≤ allocatedComparisonDimension m s) (hps : p + E ≤ s) (hPs : P ≤ s) (hQs : Q ≤ s) :
    2 * Real.exp (allocatedSiteFamilyWindowLog D + D * allocatedSiteKernelMaskLog m P + 1 +
      (coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim (p + E)) + Q)) ≤
      Real.exp (allocatedEarlyWindowSelectionLog m dim s) := by
  have hdim := (allocatedComparisonDimension_bounds m hs).1
  have hwin : allocatedSiteFamilyWindowLog D ≤ allocatedSiteFamilyWindowLog (allocatedComparisonDimension m s) := by
    unfold allocatedSiteFamilyWindowLog allocatedSiteAxisWindowLog allocatedSiteCoefficientLog
    gcongr
  have hmask : allocatedSiteKernelMaskLog m P ≤ allocatedSiteKernelMaskLog m s := by
    unfold allocatedSiteKernelMaskLog
    gcongr
  have hprod := mul_le_mul hDs hmask (allocatedSiteKernelMaskLog_nonneg m hP) hdim
  have hpE := add_nonneg hp hE
  have hinput : allocatedEarlyCoarseInput m dim (p + E) ≤ allocatedEarlyCoarseInput m dim s := by
    dsimp only [allocatedEarlyCoarseInput, anisotropicSpatialCapLog, spatialLipschitzEnvelope,
      spatialFixedProfileEnvelope, coefficientErrorVolumeLog]
    gcongr
  have hinput0 := (allocatedEarlyCoarseInput_bounds m dim hpE).1
  have hinputs0 := (allocatedEarlyCoarseInput_bounds m dim hs).1
  have hpartition : coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim (p + E)) ≤
      coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim s) := by
    dsimp only [coarseSpatialPartitionLog, coarseSpatialReciprocalLog, spatialTupleToleranceLog]
    gcongr
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  apply (mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp only [allocatedEarlyWindowSelectionLog]
  linarith only [hwin, hprod, hpartition, hQs]

theorem exists_allocatedEarlyWindowSelectionLog_bound (m dim : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ s : ℝ, 0 ≤ s → allocatedEarlyWindowSelectionLog m dim s ≤ (s + a) ^ a := by
  let poly : Polynomial ℕ := allocatedEarlyWindowSelectionLog m dim Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro s hs
  simpa [poly, allocatedEarlyWindowSelectionLog, allocatedComparisonDimension,
    allocatedSiteFamilyWindowLog, allocatedSiteAxisWindowLog, allocatedSiteCoefficientLog,
    allocatedSiteKernelMaskLog, coarseSpatialPartitionLog, coarseSpatialReciprocalLog,
    spatialTupleToleranceLog, allocatedEarlyCoarseInput, spatialLipschitzEnvelope,
    spatialFixedProfileEnvelope, anisotropicSpatialCapLog, coefficientErrorVolumeLog,
    Polynomial.eval₂_pow] using hbound s hs

end Erdos3.VectorPolynomial

end

end OAI
