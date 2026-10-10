import OAI.Combinatorics.Progressions.Estimates.AllocatedOriginalCommonResources

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedCoarseNativeLog {A : Type*} [Semiring A]
    (m dim : ℕ) (pI p0 pAccuracy w v E0 D O pc gc Pτ : A) : A :=
  coarseSpatialPartitionLog (allocatedProductCoarseInput m dim p0 pAccuracy w v E0) +
    allocatedFullGridCoefficientPreLog m D O +
    allocatedFiniteIdealMaskedLog m D pI ((m * 2 ^ (m + 1) : ℕ) * p0)
      ((m + 1 : ℕ) * p0) +
    (2 ^ (m + 1) : ℕ) * D * O + allocatedCanonicalNormalizerLog m D pc gc +
    allocatedAmbientNormalizationLog dim p0 D p0 Pτ + 1

theorem allocatedCoarseNativeLog_le_diagonal (m dim : ℕ)
    {pI p0 pAccuracy w v E0 D O pc gc Pτ t : ℝ}
    (hpI : 0 ≤ pI) (hp0 : 0 ≤ p0) (hpAccuracy : 0 ≤ pAccuracy)
    (hw : 0 ≤ w) (hv : 0 ≤ v) (hE0 : 0 ≤ E0) (hD : 0 ≤ D)
    (hO : 0 ≤ O) (hpc : 0 ≤ pc) (hgc : 0 ≤ gc) (hPτ : 0 ≤ Pτ)
    (hpIt : pI ≤ t) (hp0t : p0 ≤ t) (hpAccuracyt : pAccuracy ≤ t)
    (hwt : w ≤ t) (hvt : v ≤ t) (hE0t : E0 ≤ t) (hDt : D ≤ t)
    (hOt : O ≤ t) (hpct : pc ≤ t) (hgct : gc ≤ t) (hPτt : Pτ ≤ t) :
    allocatedCoarseNativeLog m dim pI p0 pAccuracy w v E0 D O pc gc Pτ ≤
      allocatedCoarseNativeLog m dim t t t t t t t t t t t := by
  have ht : 0 ≤ t := hpI.trans hpIt
  have hd0 := (allocatedComparisonDimension_bounds m hpAccuracy).1
  have hdt0 := (allocatedComparisonDimension_bounds m ht).1
  have hdim := allocatedComparisonDimension_mono m hpAccuracy hpAccuracyt
  have hearly : allocatedEarlyCoarseInput m dim (p0 + E0) ≤
      allocatedEarlyCoarseInput m dim (t + t) := by
    dsimp only [allocatedEarlyCoarseInput, spatialLipschitzEnvelope,
      spatialFixedProfileEnvelope, anisotropicSpatialCapLog, coefficientErrorVolumeLog]
    gcongr
  have hmass : allocatedOriginalMassLog m p0 pAccuracy w v ≤
      allocatedOriginalMassLog m t t t t := by
    dsimp only [allocatedOriginalMassLog, allocatedSiteSpatialMassLog,
      coefficientMajorantMassLog, coefficientErrorVolumeLog]
    gcongr
  have hinput0 : 0 ≤ allocatedProductCoarseInput m dim p0 pAccuracy w v E0 := by
    have he := (allocatedEarlyCoarseInput_bounds m dim (add_nonneg hp0 hE0)).1
    have hm := allocatedSiteSpatialMassLog_nonneg hd0 hw hv
    dsimp only [allocatedProductCoarseInput, allocatedOriginalMassLog, coefficientErrorVolumeLog]
    positivity
  have hinput : allocatedProductCoarseInput m dim p0 pAccuracy w v E0 ≤
      allocatedProductCoarseInput m dim t t t t t := by
    dsimp only [allocatedProductCoarseInput]
    gcongr
  have hinputt0 := hinput0.trans hinput
  have hpartition : coarseSpatialPartitionLog (allocatedProductCoarseInput m dim p0 pAccuracy w v E0) ≤
      coarseSpatialPartitionLog (allocatedProductCoarseInput m dim t t t t t) := by
    dsimp only [coarseSpatialPartitionLog, coarseSpatialReciprocalLog, spatialTupleToleranceLog]
    gcongr
  have hcommon := allocatedCommonRadiusLog_mono m hpc hgc hpct hgct
  have hdc := (allocatedComparisonDimension_bounds m hpc).1
  have hdct := allocatedComparisonDimension_mono m hpc hpct
  have hproduct := allocatedProductChartLog_mono m hdc hdct hgct
  have hradius : allocatedCommonProductRadiusLog m pc gc ≤ allocatedCommonProductRadiusLog m t t :=
    add_le_add hcommon hproduct
  have hradius0 := (allocatedCommonProductRadius_bounds m hpc hgc).1
  have hnormalizer : allocatedCanonicalNormalizerLog m D pc gc ≤
      allocatedCanonicalNormalizerLog m t t t := by
    unfold allocatedCanonicalNormalizerLog
    gcongr
  have hfinite : allocatedFiniteIdealMaskedLog m D pI
      ((m * 2 ^ (m + 1) : ℕ) * p0) ((m + 1 : ℕ) * p0) ≤
      allocatedFiniteIdealMaskedLog m t t
        ((m * 2 ^ (m + 1) : ℕ) * t) ((m + 1 : ℕ) * t) := by
    dsimp only [allocatedFiniteIdealMaskedLog, allocatedFiniteIdealCoefficientLog,
      allocatedFiniteIdealProfileLog]
    gcongr
  have hgrid : allocatedFullGridCoefficientPreLog m D O ≤
      allocatedFullGridCoefficientPreLog m t t := by
    unfold allocatedFullGridCoefficientPreLog
    gcongr
  have hambient : allocatedAmbientNormalizationLog dim p0 D p0 Pτ ≤
      allocatedAmbientNormalizationLog dim t t t t := by
    unfold allocatedAmbientNormalizationLog
    gcongr
  unfold allocatedCoarseNativeLog
  gcongr

theorem exists_allocatedCoarseNativeLog_bound (m dim : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      allocatedCoarseNativeLog m dim t t t t t t t t t t t ≤ (t + C) ^ C := by
  let poly : Polynomial ℕ := allocatedCoarseNativeLog m dim
    Polynomial.X Polynomial.X Polynomial.X Polynomial.X Polynomial.X Polynomial.X
    Polynomial.X Polynomial.X Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨C, hC, hb⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro t ht
  simpa [poly, allocatedCoarseNativeLog, allocatedProductCoarseInput, allocatedOriginalMassLog,
    allocatedSiteSpatialMassLog, coefficientMajorantMassLog, allocatedEarlyCoarseInput,
    coarseSpatialPartitionLog, coarseSpatialReciprocalLog, spatialTupleToleranceLog,
    anisotropicSpatialCapLog, spatialLipschitzEnvelope, spatialFixedProfileEnvelope,
    coefficientErrorVolumeLog, allocatedFullGridCoefficientPreLog,
    allocatedFiniteIdealMaskedLog, allocatedFiniteIdealCoefficientLog, allocatedFiniteIdealProfileLog,
    allocatedCanonicalNormalizerLog, allocatedAmbientNormalizationLog,
    allocatedCommonProductRadiusLog, allocatedCommonRadiusLog, allocatedBufferedRadiusLog,
    allocatedBufferedRadiusInput, allocatedProductChartLog, allocatedIdealCoverPrimitiveLog,
    allocatedIdealCoverInputLog, allocatedSiteCoefficientLog, allocatedComparisonDimension,
    Polynomial.eval₂_pow] using hb t ht

end Erdos3.VectorPolynomial

end

end OAI
