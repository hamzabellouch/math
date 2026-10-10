import OAI.Analysis.OperatorAlgebra.VectorLpStrongConvergence
import OAI.Analysis.OperatorAlgebra.ScalarLpLocalizedFunctions
import OAI.Analysis.ModularTheory.FourierTranslation

namespace OAI

/-! Bounded continuous functions of regular translation belong to the
actual modular core. Bounded spectral charts reduce the statement to its
character generators; no spectral projection is postulated. -/

noncomputable section
open MeasureTheory Filter Set FourierTransform
open scoped Topology CStarAlgebra

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Functional calculus for regular translation, in the Fourier convention
fixed by `fourier_modularLpTranslate`. -/
def modularTranslationCalculus : BoundedContinuousFunction ℝ ℂ →⋆ₐ[ℂ]
    (Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) :=
  (Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv.toStarAlgHom.comp
    (vectorLpRepresentation volume)

lemma modularTranslationCalculus_apply (g : BoundedContinuousFunction ℝ ℂ)
    (f : Lp H 2 (volume : Measure ℝ)) :
    modularTranslationCalculus g f = 𝓕⁻ (vectorLpRepresentation volume g (𝓕 f)) := rfl

lemma modularTranslationCalculus_character (r : ℝ) :
    modularTranslationCalculus (H := H) (BoundedRecovery.spectralCharacter r) =
      (modularLpTranslateEquiv (H := H) volume (r / (-2 * Real.pi)) :
        Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) := by
  have hr : -2 * Real.pi * (r / (-2 * Real.pi)) = r := by field_simp [Real.pi_ne_zero]
  apply ContinuousLinearMap.ext
  intro f
  apply (Lp.fourierTransformₗᵢ ℝ H).injective
  change 𝓕 (𝓕⁻ (vectorLpRepresentation volume (BoundedRecovery.spectralCharacter r) (𝓕 f))) =
    𝓕 (modularLpTranslate volume (r / (-2 * Real.pi)) f)
  rw [fourier_fourierInv_eq, fourier_modularLpTranslate, hr,
    vectorLpRepresentation_character]
  rfl

variable (S : BoundedRecovery.StandardModularData H)

lemma modularTranslationCalculus_phaseCosine_mem (r c : ℝ) :
    modularTranslationCalculus (H := H) (scalarPhaseCosine r c) ∈
      modularCrossedProduct (volume : Measure ℝ) S := by
  have hx : modularTranslationCalculus (H := H)
      ((BoundedRecovery.spectralCharacter c 1) • BoundedRecovery.spectralCharacter r) ∈
      modularCrossedProduct (volume : Measure ℝ) S := by
    rw [map_smul, modularTranslationCalculus_character]
    exact (modularCrossedProduct volume S).toStarSubalgebra.smul_mem
      (modularCrossedProduct_translate volume S _) _
  rw [scalarPhaseCosine_character, map_smul, map_add, map_star]
  exact (modularCrossedProduct volume S).toStarSubalgebra.smul_mem (add_mem hx (star_mem hx)) _

lemma modularTranslationCalculus_chart_mem (n : ℕ) (g : BoundedContinuousFunction ℝ ℂ) :
    modularTranslationCalculus (H := H) (intervalChartFunction n g) ∈
      modularCrossedProduct (volume : Measure ℝ) S := by
  let Φ := modularTranslationCalculus (H := H)
  let a := scalarPhaseCosine (intervalChartRate n) (intervalChartRate n * n)
  let f : ℂ → ℂ := fun z => g (Real.arccos z.re / intervalChartRate n - n)
  have hf : Continuous f := g.continuous.comp
    ((Real.continuous_arccos.comp Complex.continuous_re).div_const
      (intervalChartRate n) |>.sub continuous_const)
  have : ContinuousFunctionalCalculus ℂ
      (Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
      (A := Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
  have ha : IsStarNormal a := (scalarPhaseCosine_selfAdjoint _ _).isStarNormal
  change Φ (cfc f a) ∈ modularCrossedProduct volume S
  rw [Φ.map_cfc f a hf.continuousOn (ha := ha) (hφa := ha.map Φ)]
  let : IsClosed ((modularCrossedProduct volume S).toStarSubalgebra :
      Set (Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))) :=
    BoundedRecovery.vonNeumannAlgebra_isClosed _
  change cfc f (Φ a) ∈ (modularCrossedProduct volume S).toStarSubalgebra
  exact cfc_mem (𝕜' := ℂ) f (show Φ a ∈
    (modularCrossedProduct volume S).toStarSubalgebra from
      modularTranslationCalculus_phaseCosine_mem S _ _)

lemma intervalChartFunction_norm_le (n : ℕ) (g : BoundedContinuousFunction ℝ ℂ) (t : ℝ) :
    ‖intervalChartFunction n g t‖ ≤ ‖g‖ := by
  rw [intervalChartFunction, scalarPhaseCosine_cfc_apply]
  · exact g.norm_coe_le_norm _
  · exact g.continuous.comp ((Real.continuous_arccos.comp Complex.continuous_re).div_const
      (intervalChartRate n) |>.sub continuous_const)

lemma intervalChartFunction_tendsto (g : BoundedContinuousFunction ℝ ℂ) (t : ℝ) :
    Tendsto (fun n => intervalChartFunction n g t) atTop (𝓝 (g t)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt |t|
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have ht : t ∈ Icc (-(n : ℝ)) n := abs_le.mp (hN.le.trans (by exact_mod_cast hn))
  exact (intervalChartFunction_apply n g ht).symm

lemma modularTranslationCalculus_chart_strong (g : BoundedContinuousFunction ℝ ℂ)
    (f : Lp H 2 (volume : Measure ℝ)) :
    Tendsto (fun n => modularTranslationCalculus (intervalChartFunction n g) f)
      atTop (𝓝 (modularTranslationCalculus g f)) := by
  have h := vectorLpRepresentation_strong (fun n => intervalChartFunction n g)
    g g.continuous.aestronglyMeasurable ‖g‖ (norm_nonneg _)
    (fun n t => intervalChartFunction_norm_le n g t) g.norm_coe_le_norm
    (intervalChartFunction_tendsto g) (𝓕 f)
  exact (Lp.fourierTransformₗᵢ ℝ H).symm.continuous.continuousAt.tendsto.comp h

/-- Every bounded continuous regular-translation multiplier lies in the core. -/
theorem modularTranslationCalculus_mem (g : BoundedContinuousFunction ℝ ℂ) :
    modularTranslationCalculus (H := H) g ∈ modularCrossedProduct (volume : Measure ℝ) S := by
  rw [← (modularCrossedProduct volume S).commutant_commutant,
    VonNeumannAlgebra.mem_commutant_iff]
  intro b hb
  exact (commute_of_strong_limit b (modularTranslationCalculus g)
    (fun n => modularTranslationCalculus (intervalChartFunction n g))
    (fun n => ((VonNeumannAlgebra.mem_commutant_iff.mp hb) _
      (modularTranslationCalculus_chart_mem S n g)).symm)
    (modularTranslationCalculus_chart_strong g)).eq

end WeakPureInfiniteness

end

end OAI
