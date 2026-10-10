import OAI.Analysis.KadisonKastler.PublishedRegularDiagonal
import Mathlib.Analysis.Fourier.LpSpace

namespace OAI

/-! # The concrete Fourier frequency projections

The Fourier transform uses mathlib's `exp(-2*pi*i*t*ξ)` convention.
Thus the cut of the generator `-i d/dt` at `a` is the Fourier multiplier
of `Ioi (a/(2*pi))`. The upper frequency cuts decrease with `a`; negating
the index gives the increasing chain used by the nest distance theorem.
-/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Multiplication by the indicator of a measurable subset of the line. -/
def regularIndicatorProjection (s : Set ℝ) (hs : MeasurableSet s) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  regularScalarMultiplier (s.indicator fun _ => (1 : ℂ))
    (measurable_const.indicator hs) 1 (by
      intro t
      by_cases ht : t ∈ s <;> simp [ht])

omit [CompleteSpace H] in
theorem regularIndicatorProjection_apply_ae (s : Set ℝ) (hs : MeasurableSet s)
    (f : RegularCoreHilbert H) :
    regularIndicatorProjection s hs f =ᵐ[volume] s.indicator f := by
  filter_upwards [regularFieldOperator_represents volume
    (fun t => (s.indicator (fun _ => (1 : ℂ))) t • (1 : H →L[ℂ] H))
    (fun ξ => (measurable_const.indicator hs).aestronglyMeasurable.smul_const ξ)
    1 (show ∀ᵐ t : ℝ, ‖(s.indicator (fun _ => (1 : ℂ))) t • (1 : H →L[ℂ] H)‖ ≤ 1 from
      Filter.Eventually.of_forall fun t => by
        by_cases ht : t ∈ s
        · simp only [Set.indicator_of_mem ht, one_smul]
          exact ContinuousLinearMap.norm_id_le
        · simp [ht]) f] with t ht
  change regularIndicatorProjection s hs f t = _ at ht
  rw [ht]
  by_cases h : t ∈ s <;> simp [h]

omit [CompleteSpace H] in
theorem regularIndicatorProjection_mul_of_subset (s t : Set ℝ)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s ⊆ t) :
    regularIndicatorProjection (H := H) s hs * regularIndicatorProjection t ht =
      regularIndicatorProjection s hs := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae s hs
      (regularIndicatorProjection t ht f),
    regularIndicatorProjection_apply_ae t ht f,
    regularIndicatorProjection_apply_ae s hs f] with x h₁ h₂ h₃
  change regularIndicatorProjection s hs (regularIndicatorProjection t ht f) x =
    regularIndicatorProjection s hs f x
  rw [h₁, h₃]
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx]
    rw [h₂, Set.indicator_of_mem (hst hx)]
  · simp only [Set.indicator_of_notMem hx]

theorem regularIndicatorProjection_isStarProjection (s : Set ℝ) (hs : MeasurableSet s) :
    IsStarProjection (regularIndicatorProjection (H := H) s hs) := by
  refine ⟨regularIndicatorProjection_mul_of_subset s s hs hs Set.Subset.rfl, ?_⟩
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℂ (regularIndicatorProjection s hs f) g =
    inner ℂ f (regularIndicatorProjection s hs g)
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [regularIndicatorProjection_apply_ae s hs f,
    regularIndicatorProjection_apply_ae s hs g] with x hf hg
  rw [hf, hg]
  by_cases hx : x ∈ s <;> simp [hx]

/-- The positive-frequency cut of the actual `L²` Fourier transform. -/
def regularFrequencyProjection (a : ℝ) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  (Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv
    (regularIndicatorProjection (Set.Ioi (a / (2 * Real.pi))) measurableSet_Ioi)

theorem regularFrequencyProjection_isStarProjection (a : ℝ) :
    IsStarProjection (regularFrequencyProjection (H := H) a) :=
  (regularIndicatorProjection_isStarProjection (H := H)
    (Set.Ioi (a / (2 * Real.pi))) measurableSet_Ioi).map
      (Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv

theorem regularFrequencyProjection_apply_fourier (a : ℝ) (f : RegularCoreHilbert H) :
    (𝓕 (regularFrequencyProjection a f) : RegularCoreHilbert H) =ᵐ[volume]
      (Set.Ioi (a / (2 * Real.pi))).indicator (𝓕 f : RegularCoreHilbert H) := by
  change (Lp.fourierTransformₗᵢ ℝ H)
    ((Lp.fourierTransformₗᵢ ℝ H).symm
      (regularIndicatorProjection (Set.Ioi (a / (2 * Real.pi))) measurableSet_Ioi
        ((Lp.fourierTransformₗᵢ ℝ H) f))) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact regularIndicatorProjection_apply_ae _ _ _

/-- Upper frequency cuts decrease as the threshold increases. -/
theorem regularFrequencyProjection_mul (a b : ℝ) (hab : a ≤ b) :
    regularFrequencyProjection (H := H) b * regularFrequencyProjection a =
      regularFrequencyProjection b := by
  have hsub : Set.Ioi (b / (2 * Real.pi)) ⊆ Set.Ioi (a / (2 * Real.pi)) :=
    Set.Ioi_subset_Ioi (div_le_div_of_nonneg_right hab (by positivity))
  exact (map_mul (Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv _ _).symm.trans
    (congrArg (Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv
      (regularIndicatorProjection_mul_of_subset _ _ _ _ hsub))

/-- Reindexing the upper cuts produces an increasing real-indexed nest. -/
def regularFrequencyNest (a : ℝ) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H := regularFrequencyProjection (-a)

theorem regularFrequencyNest_isStarProjection (a : ℝ) :
    IsStarProjection (regularFrequencyNest (H := H) a) :=
  regularFrequencyProjection_isStarProjection _

theorem regularFrequencyNest_mono (a b : ℝ) (hab : a ≤ b) :
    regularFrequencyNest (H := H) a * regularFrequencyNest b = regularFrequencyNest a :=
  regularFrequencyProjection_mul (-b) (-a) (neg_le_neg hab)

end

end KadisonKastler

end OAI
