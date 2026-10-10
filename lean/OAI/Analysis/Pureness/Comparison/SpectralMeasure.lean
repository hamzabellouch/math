import OAI.Analysis.Pureness.Comparison.TraceFunctionalCalculus
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

namespace OAI
open scoped ComplexOrder ENNReal
open MeasureTheory CompactlySupported CompactlySupportedContinuousMap
namespace CuntzComparison
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

noncomputable def TracialState.spectralFunctional (τ : TracialState A)
    (a : A) (ha : IsSelfAdjoint a) : C_c(spectrum ℝ a, ℝ) →ₚ[ℝ] ℝ where
  toFun f := (τ.toPositiveLinearMap (cfcHom ha f.toContinuousMap)).re
  map_add' f g := by
    change (τ.toPositiveLinearMap (cfcHom ha (f.toContinuousMap + g.toContinuousMap))).re = _
    simp only [map_add, Complex.add_re]
  map_smul' r f := by
    change (τ.toPositiveLinearMap (cfcHom ha (r • f.toContinuousMap))).re = _
    rw [map_smul]
    change ((τ.toPositiveLinearMap.toLinearMap.restrictScalars ℝ)
      (r • cfcHom ha f.toContinuousMap)).re = _
    rw [map_smul]
    simp
  monotone' f g h := by
    apply (Complex.le_def.mp (τ.toPositiveLinearMap.monotone ?_)).1
    apply sub_nonneg.mp
    rw [← map_sub]
    apply (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _
      (cfcHom_predicate ha _)).mpr
    intro t ht
    rw [cfcHom_map_spectrum] at ht
    obtain ⟨x, rfl⟩ := ht
    exact sub_nonneg.mpr (h x)

noncomputable def TracialState.spectralMeasureOn (τ : TracialState A)
    (a : A) (ha : IsSelfAdjoint a) : Measure (spectrum ℝ a) :=
  RealRMK.rieszMeasure (τ.spectralFunctional a ha)

instance (τ : TracialState A) (a : A) (ha : IsSelfAdjoint a) :
    IsFiniteMeasure (τ.spectralMeasureOn a ha) := by
  unfold TracialState.spectralMeasureOn
  infer_instance

instance (τ : TracialState A) (a : A) (ha : IsSelfAdjoint a) :
    (τ.spectralMeasureOn a ha).Regular := by
  unfold TracialState.spectralMeasureOn
  infer_instance

noncomputable def TracialState.spectralMeasure (τ : TracialState A)
    (a : A) (ha : IsSelfAdjoint a) : Measure ℝ :=
  (τ.spectralMeasureOn a ha).map Subtype.val

instance (τ : TracialState A) (a : A) (ha : IsSelfAdjoint a) :
    IsFiniteMeasure (τ.spectralMeasure a ha) := by
  unfold TracialState.spectralMeasure
  infer_instance

instance (τ : TracialState A) (a : A) (ha : IsSelfAdjoint a) :
    (τ.spectralMeasure a ha).Regular := by
  unfold TracialState.spectralMeasure
  infer_instance

theorem TracialState.integral_spectralMeasure (τ : TracialState A)
    (a : A) (ha : IsSelfAdjoint a) (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ t, f t ∂(τ.spectralMeasure a ha) = (τ.toPositiveLinearMap (cfc f a)).re := by
  let g : C_c(spectrum ℝ a, ℝ) :=
    ⟨⟨fun t => f t, hf.comp continuous_subtype_val⟩, HasCompactSupport.of_compactSpace _⟩
  rw [TracialState.spectralMeasure, integral_map (by fun_prop) (by fun_prop)]
  change ∫ t, g t ∂(RealRMK.rieszMeasure (τ.spectralFunctional a ha)) = _
  rw [RealRMK.integral_rieszMeasure]
  change (τ.toPositiveLinearMap (cfcHom ha g.toContinuousMap)).re = _
  rw [cfc_apply f a ha hf.continuousOn]
  rfl

theorem TracialState.linking_spectralMeasure (τ : TracialState A) (z : A) :
    τ.spectralMeasure (star z * z) (star_mul_self_nonneg z).isSelfAdjoint =
      τ.spectralMeasure (z * star z) (mul_star_self_nonneg z).isSelfAdjoint := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [τ.integral_spectralMeasure _ _ f f.continuous,
    τ.integral_spectralMeasure _ _ f f.continuous,
    τ.linking_cfc_trace z f f.continuous]

noncomputable def TracialState.spectralSupportMass (τ : TracialState A)
    (a : A) (ha : 0 ≤ a) : ℝ≥0∞ :=
  τ.spectralMeasure a ha.isSelfAdjoint (Set.Ioi 0)

theorem TracialState.linking_support_mass (τ : TracialState A) (z : A) :
    τ.spectralSupportMass (star z * z) (star_mul_self_nonneg z) =
      τ.spectralSupportMass (z * star z) (mul_star_self_nonneg z) := by
  unfold TracialState.spectralSupportMass
  rw [τ.linking_spectralMeasure]
end CuntzComparison

end OAI
