import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalRellich
import OAI.Geometry.PrescribedRicci.GlobalKahlerIntegral

namespace OAI

/-! Coordinate Volume Comparison. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped SchwartzMap ContDiff Classical
namespace EllipticKernel

instance coordinateMap_haar (d : ℕ) :
    (Measure.map (coordinateEquiv d) (volume : Measure (EC d))).IsAddHaarMeasure :=
  (coordinateEquiv d).isAddHaarMeasure_map _

def coordinateVolumeFactor (d : ℕ) : ℝ :=
  Measure.addHaarScalarFactor (Measure.map (coordinateEquiv d) (volume : Measure (EC d))) volume

lemma coordinateVolumeFactor_pos (d : ℕ) : 0 < coordinateVolumeFactor d :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

lemma integral_coordinates (d : ℕ) {F : Anticanonical.Coordinates d → ℝ} (hF : Continuous F) :
    (∫ z : EC d, F (coordinateEquiv d z)) = coordinateVolumeFactor d * ∫ z, F z := by
  rw [← integral_map (coordinateEquiv d).continuous.measurable.aemeasurable hF.aestronglyMeasurable,
    Measure.isAddLeftInvariant_eq_smul (Measure.map (coordinateEquiv d) volume) volume,
    integral_smul_nnreal_measure]
  rfl

end EllipticKernel
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma schwartzCoord_zero_eq (f : 𝓢(E, ℂ)) : schwartzCoord 0 f = f.toLp 2 := by
  apply realize_injective 0
  rw [realize_schwartzCoord, realize_zero]
  exact (Lp.toTemperedDistribution_toLp_eq f).symm

lemma norm_sq_schwartzCoord_zero (f : 𝓢(E, ℂ)) :
    ‖schwartzCoord 0 f‖ ^ 2 = ∫ z, ‖f z‖ ^ 2 := by
  rw [schwartzCoord_zero_eq]
  have hi := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (f.toLp 2)
  rw [SchwartzMap.inner_toL2_toL2_eq f f volume] at hi
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] at hi
  rw [integral_ofReal] at hi
  exact (RCLike.ofReal_injective hi).symm

end SobolevChart
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X}

lemma norm_localize_coordinates (i : Fin A.count) (ρ f : Smooth A)
    (hs : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart i).source) (z : EC d) :
    ‖localize A i ρ hs f z‖ ^ 2 =
      KaehlerMetric.localizeFunction i (fun x => ‖ρ x * f x‖ ^ 2) (coordinateEquiv d z) := by
  by_cases hz : z ∈ (A.euclideanChart i).target
  · have hz' : coordinateEquiv d z ∈ (A.chart i).target := by simpa using hz
    simp only [localize_apply, localizeFun, ite_eq_left hz,
      KaehlerMetric.localizeFunction, ite_eq_left hz']
    rfl
  · have hz' : coordinateEquiv d z ∉ (A.chart i).target := by simpa using hz
    simp only [localize_apply, localizeFun, ite_eq_right hz,
      KaehlerMetric.localizeFunction, ite_eq_right hz', norm_zero, zero_pow (by decide : 2 ≠ 0)]

lemma norm_sq_localize_integral (i : Fin A.count) (ρ f : Smooth A)
    (hs : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart i).source) :
    ‖schwartzCoord 0 (localize A i ρ hs f)‖ ^ 2 =
      coordinateVolumeFactor d * ∫ z, KaehlerMetric.localizeFunction i (fun x => ‖ρ x * f x‖ ^ 2) z := by
  rw [norm_sq_schwartzCoord_zero]
  simp_rw [norm_localize_coordinates]
  apply integral_coordinates
  apply (KaehlerMetric.localizeFunction_continuous_compact i
    ((ρ.continuous.mul f.continuous).norm.pow 2) ?_).1
  refine Subset.trans (closure_minimal ?_ (isClosed_tsupport (ρ : X → ℂ))) (by simpa using hs)
  intro x hx
  apply subset_tsupport
  change ρ x ≠ 0
  intro h
  have : ‖ρ x * f x‖ ^ 2 = 0 := by rw [h, zero_mul, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  exact hx this

end GlobalElliptic

end
end

end OAI
