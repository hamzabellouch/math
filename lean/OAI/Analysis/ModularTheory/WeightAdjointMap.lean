import OAI.Analysis.ModularTheory.NormalAdjointWeight

namespace OAI

/-! A norm-preserving conjugate-linear map on the actual core GNS Hilbert
space. Gauge removal and Fourier transform turn a normal-ordered weight
vector into its scalar frequency coefficient before modular conjugation. -/

noncomputable section
open MeasureTheory FourierTransform

namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : StandardModularData H)

def modularConjugationLp : Lp H 2 (volume : Measure ℝ) →SL[starRingEnd ℂ]
    Lp H 2 (volume : Measure ℝ) :=
  S.J.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 volume

lemma modularConjugationLp_ae (f : Lp H 2 (volume : Measure ℝ)) :
    modularConjugationLp S f =ᵐ[volume] fun t => S.J (f t) :=
  S.J.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL f

lemma modularConjugationLp_norm (f : Lp H 2 (volume : Measure ℝ)) :
    ‖modularConjugationLp S f‖ = ‖f‖ := by
  have h : ‖modularConjugationLp S f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [vectorLp_norm_sq_integral, vectorLp_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [modularConjugationLp_ae S f] with t ht
    rw [ht, S.J.norm_map]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

def modularWeightAdjointMap (f : Lp H 2 (volume : Measure ℝ)) :
    Lp H 2 (volume : Measure ℝ) :=
  𝓕⁻ (modularConjugationLp S (𝓕 (S.D.lpGauge volume 1 f)))

lemma modularWeightAdjointMap_norm (f : Lp H 2 (volume : Measure ℝ)) :
    ‖modularWeightAdjointMap S f‖ = ‖f‖ := by
  change ‖(Lp.fourierTransformₗᵢ ℝ H).symm
    (modularConjugationLp S (𝓕 (S.D.lpGauge volume 1 f)))‖ = _
  rw [(Lp.fourierTransformₗᵢ ℝ H).symm.norm_map, modularConjugationLp_norm,
    Lp.norm_fourier_eq, S.D.lpGauge_norm]

lemma modularWeightAdjointMap_add (f h : Lp H 2 (volume : Measure ℝ)) :
    modularWeightAdjointMap S (f + h) =
      modularWeightAdjointMap S f + modularWeightAdjointMap S h := by
  change (Lp.fourierTransformₗᵢ ℝ H).symm
      (modularConjugationLp S ((Lp.fourierTransformₗᵢ ℝ H) (S.D.lpGauge volume 1 (f + h)))) =
    (Lp.fourierTransformₗᵢ ℝ H).symm
      (modularConjugationLp S ((Lp.fourierTransformₗᵢ ℝ H) (S.D.lpGauge volume 1 f))) +
    (Lp.fourierTransformₗᵢ ℝ H).symm
      (modularConjugationLp S ((Lp.fourierTransformₗᵢ ℝ H) (S.D.lpGauge volume 1 h)))
  rw [S.D.lpGauge_add, map_add, map_add, map_add]

lemma modularWeightAdjointMap_continuous : Continuous (modularWeightAdjointMap S) :=
  (Lp.fourierTransformₗᵢ ℝ H).symm.continuous.comp
    ((modularConjugationLp S).continuous.comp
      ((Lp.fourierTransformₗᵢ ℝ H).continuous.comp (S.D.lpGaugeEquiv volume 1).continuous))

end WeakPureInfiniteness

end

end OAI
