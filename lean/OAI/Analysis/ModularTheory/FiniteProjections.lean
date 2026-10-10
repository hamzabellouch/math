import OAI.Analysis.OperatorAlgebra.VectorLpProjection
import OAI.Analysis.ModularTheory.CoreTracial

namespace OAI

/-! Finite-weight Fourier interval projections in the actual modular core. -/

noncomputable section
open MeasureTheory Filter Set FourierTransform
open scoped Topology ENNReal

namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def modularFiniteProjection (n : ℕ) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  (Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv
    (vectorLpProjection (Icc (-(n : ℝ)) n) measurableSet_Icc)

lemma modularFiniteProjection_apply (n : ℕ) (f : Lp H 2 (volume : Measure ℝ)) :
    modularFiniteProjection n f =
      𝓕⁻ (vectorLpProjection (Icc (-(n : ℝ)) n) measurableSet_Icc (𝓕 f)) := rfl

lemma modularFiniteProjection_isStarProjection (n : ℕ) :
    IsStarProjection (modularFiniteProjection (H := H) n) := by
  exact (vectorLpProjection_isStarProjection (H := H) _ measurableSet_Icc).map
    (Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv

lemma modularFiniteProjection_norm_le (n : ℕ) :
    ‖modularFiniteProjection (H := H) n‖ ≤ 1 := by
  change ‖(Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv
    (vectorLpProjection _ _)‖ ≤ 1
  rw [StarAlgEquiv.norm_map]
  exact vectorLpProjection_norm_le _ _

lemma modularFiniteProjection_mem (S : StandardModularData H) (n : ℕ) :
    modularFiniteProjection n ∈ modularCrossedProduct (volume : Measure ℝ) S := by
  have hs (f : Lp H 2 (volume : Measure ℝ)) :
      Tendsto (fun k => modularTranslationCalculus (vectorIntervalCutoff n k) f)
        atTop (𝓝 (modularFiniteProjection n f)) :=
    (Lp.fourierTransformₗᵢ ℝ H).symm.continuous.continuousAt.tendsto.comp
      (vectorIntervalCutoff_strong n (𝓕 f))
  rw [← (modularCrossedProduct volume S).commutant_commutant,
    VonNeumannAlgebra.mem_commutant_iff]
  intro b hb
  exact (commute_of_strong_limit b (modularFiniteProjection n)
    (fun k => modularTranslationCalculus (vectorIntervalCutoff n k))
    (fun k => ((VonNeumannAlgebra.mem_commutant_iff.mp hb) _
      (modularTranslationCalculus_mem S _)).symm) hs).eq

lemma vectorLpProjection_scalarInclusion (S : StandardModularData H) (n : ℕ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    vectorLpProjection (Icc (-(n : ℝ)) n) measurableSet_Icc
        (modularScalarInclusion volume S f) =
      modularScalarInclusion volume S (scalarIntervalProjection n f) := by
  apply Lp.ext
  filter_upwards [vectorLpProjection_ae (Icc (-(n : ℝ)) n) measurableSet_Icc
    (modularScalarInclusion volume S f), modularScalarInclusion_ae volume S f,
    modularScalarInclusion_ae volume S (scalarIntervalProjection n f),
    scalarIntervalProjection_ae n f] with t hp hi hi' hs
  rw [hp, hi', hs]
  by_cases ht : t ∈ Icc (-(n : ℝ)) n <;> simp [ht, hi]

lemma modularFiniteProjection_fourierInclusion (S : StandardModularData H) (n : ℕ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    modularFiniteProjection n (modularFourierInclusion S f) =
      modularFourierInclusion S (scalarIntervalProjection n f) := by
  change 𝓕⁻ (vectorLpProjection (Icc (-(n : ℝ)) n) measurableSet_Icc
    (𝓕 ((ContinuousLinearMap.toSpanSingleton ℂ S.xi).compLpL 2 volume (𝓕⁻ f)))) =
      (ContinuousLinearMap.toSpanSingleton ℂ S.xi).compLpL 2 volume
        (𝓕⁻ (scalarIntervalProjection n f))
  rw [fourier_compLp, fourier_fourierInv_eq]
  change 𝓕⁻ (vectorLpProjection (Icc (-(n : ℝ)) n) measurableSet_Icc
    (modularScalarInclusion volume S f)) = _
  rw [vectorLpProjection_scalarInclusion]
  exact fourierInv_compLp _ _

lemma modularFiniteProjection_weightVector (S : StandardModularData H)
    (n m : ℕ) (hnm : n ≤ m) :
    modularFiniteProjection n (modularCoreWeightVector S m) = modularCoreWeightVector S n := by
  rw [modularCoreWeightVector, modularFiniteProjection_fourierInclusion,
    modularWeightCutoffVector_project n m hnm]
  rfl

lemma modularFiniteProjection_weightVector_comm (S : StandardModularData H) (n m : ℕ) :
    modularFiniteProjection n (modularCoreWeightVector S m) =
      modularFiniteProjection m (modularCoreWeightVector S n) := by
  simp only [modularCoreWeightVector, modularFiniteProjection_fourierInclusion]
  congr 1
  apply Lp.ext
  filter_upwards [scalarIntervalProjection_ae n (modularWeightCutoffVector m),
    scalarIntervalProjection_ae m (modularWeightCutoffVector n),
    modularWeightCutoffVector_ae n, modularWeightCutoffVector_ae m] with t hn hm hvn hvm
  rw [hn, hm]
  by_cases htn : t ∈ Icc (-(n : ℝ)) n <;>
    by_cases htm : t ∈ Icc (-(m : ℝ)) m <;>
      simp [htn, htm, hvn, hvm, modularWeightCutoffFunction]

lemma modularFiniteProjection_weight (S : StandardModularData H) (n : ℕ) :
    modularCoreSquareWeight S (modularFiniteProjection n) =
      ENNReal.ofReal (‖modularCoreWeightVector S n‖ ^ 2) := by
  apply le_antisymm
  · apply iSup_le
    intro m
    apply ENNReal.ofReal_le_ofReal
    rw [modularFiniteProjection_weightVector_comm S n m]
    gcongr
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by
      have h := modularFiniteProjection_norm_le (H := H) m
      simpa only [one_mul] using mul_le_mul_of_nonneg_right h
        (norm_nonneg (modularCoreWeightVector S n)))
  · have h := le_iSup (fun m : ℕ => ENNReal.ofReal
      (‖modularFiniteProjection n (modularCoreWeightVector S m)‖ ^ 2)) n
    rwa [modularFiniteProjection_weightVector S n n le_rfl] at h

lemma modularFiniteProjection_finite (S : StandardModularData H) (n : ℕ) :
    modularCoreSquareWeight S (modularFiniteProjection n) < ⊤ := by
  rw [modularFiniteProjection_weight]
  exact ENNReal.ofReal_lt_top

lemma modularFiniteProjection_weightGNS (S : StandardModularData H) (n : ℕ) :
    modularWeightVector S (modularFiniteProjection n) (modularFiniteProjection_mem S n)
      (modularFiniteProjection_finite S n) = modularCoreWeightVector S n := by
  apply tendsto_nhds_unique (modularWeightVector_tendsto S _ _ _)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with m hm
  exact (modularFiniteProjection_weightVector S n m hm).symm

end WeakPureInfiniteness

end

end OAI
