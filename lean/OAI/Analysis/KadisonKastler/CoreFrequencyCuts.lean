import OAI.Analysis.KadisonKastler.RegularCommutantFourier
import OAI.Analysis.KadisonKastler.FrequencyNest

namespace OAI

/-! # Frequency windows in the concrete modular core

The translation generators and the proved real spectral commutant theorem
put the Fourier interval projections inside the actual generated core.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (M : VonNeumannAlgebra H)

theorem regularFourierIndicator_mem_core (s : Set ℝ) (hs : MeasurableSet s) :
    (Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv (regularIndicatorProjection s hs) ∈
      regularCoreAlgebra U hU M := by
  rw [← VonNeumannAlgebra.commutant_commutant (regularCoreAlgebra U hU M)]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  have htrans (t : Multiplicative ℝ) : Commute T
      (regularRightTranslation (H := H) t : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
    (VonNeumannAlgebra.mem_commutant_iff.mp hT _ (regularTranslation_mem_core U hU M t)).symm
  have hc := commute_scalarMultiplier_of_characters
    ((Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv T)
    (fourier_commute_characters_of_translations T htrans)
    (s.indicator fun _ => (1 : ℂ)) (measurable_const.indicator hs) 1
    (fun t => by by_cases ht : t ∈ s <;> simp [ht])
  change _ = _
  apply (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv.injective
  have he : (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv
      ((Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv (regularIndicatorProjection s hs)) =
        regularIndicatorProjection s hs := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.symm_apply_apply]
  rw [map_mul, map_mul]
  change (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv T *
      (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv
        ((Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv (regularIndicatorProjection s hs)) =
    (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv
        ((Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv (regularIndicatorProjection s hs)) *
      (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv T
  rw [he]
  exact hc.eq

theorem regularFrequencyProjection_mem_core (a : ℝ) :
    regularFrequencyProjection (H := H) a ∈ regularCoreAlgebra U hU M :=
  regularFourierIndicator_mem_core U hU M _ measurableSet_Ioi

/-- A bounded frequency interval, used for the finite-weight core corners. -/
def regularFrequencyWindow (a b : ℝ) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  (Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv
    (regularIndicatorProjection (Set.Ioc a b) measurableSet_Ioc)

theorem regularFrequencyWindow_mem_core (a b : ℝ) :
    regularFrequencyWindow (H := H) a b ∈ regularCoreAlgebra U hU M :=
  regularFourierIndicator_mem_core U hU M _ measurableSet_Ioc

theorem regularFrequencyWindow_isStarProjection (a b : ℝ) :
    IsStarProjection (regularFrequencyWindow (H := H) a b) :=
  (regularIndicatorProjection_isStarProjection (H := H) _ measurableSet_Ioc).map
    (Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv

end

end KadisonKastler

end OAI
