import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model
import OAI.Analysis.JiangSu.DimensionFunctions.DimensionContentMeasure

namespace OAI


noncomputable section
namespace Pureness
open Set TopologicalSpace MeasureTheory
open scoped NNReal ENNReal

variable {X : Type*} [TopologicalSpace X]

def continuousDimensionIntegral (r : C(X, ℝ≥0) → ℝ≥0∞) (f : C(X, ℝ≥0)) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), r (continuousNNRealCut t.toNNReal f)

variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

theorem continuousDimensionIntegral_eq_lintegral
    (r : C(X, ℝ≥0) → ℝ≥0∞) (hfinite : r 1 ≠ ⊤)
    (hmono : Monotone r) (hsub : ∀ f g, r (f+g) ≤ r f+r g)
    (horth : ∀ f g, f*g = 0 → r (f+g) = r f+r g)
    (hsupport : ∀ f g, (∀ x, 0 < f x → 0 < g x) → r f ≤ r g)
    (hcuts : ∀ f, r f = ⨆ (ε : ℝ≥0) (_ : 0 < ε), r (continuousNNRealCut ε f))
    (f : C(X, ℝ≥0)) :
    continuousDimensionIntegral r f =
      ∫⁻ x, (f x : ℝ≥0∞) ∂(dimensionContent r hfinite hmono hsub horth).measure := by
  let μ := (dimensionContent r hfinite hmono hsub horth).measure
  have hm : Measurable (fun x => (f x : ℝ)) := (NNReal.continuous_coe.comp f.continuous).measurable
  have layerCake : (∫⁻ point, (f point : ℝ≥0∞) ∂μ) =
      ∫⁻ level in Ioi (0 : ℝ), μ {point | level < (f point : ℝ)} := by
    calc
      _ = ∫⁻ point, ENNReal.ofReal (f point : ℝ) ∂μ := by
        apply lintegral_congr
        intro point
        exact ENNReal.ofReal_coe_nnreal.symm
      _ = _ := lintegral_eq_lintegral_meas_lt μ
        (Filter.Eventually.of_forall (fun point => (f point).2)) hm.aemeasurable
  rw [layerCake]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change r (continuousNNRealCut t.toNNReal f) = μ {x | t < (f x : ℝ)}
  rw [← dimensionContent_measure_support r hfinite hmono hsub horth hsupport hcuts]
  congr 1
  ext x
  change 0 < f x-t.toNNReal ↔ t < (f x : ℝ)
  rw [tsub_pos_iff_lt]
  exact Real.toNNReal_lt_iff_lt_coe (show 0 ≤ t from le_of_lt ht)

theorem continuousDimensionIntegral_add
    (r : C(X, ℝ≥0) → ℝ≥0∞) (hfinite : r 1 ≠ ⊤)
    (hmono : Monotone r) (hsub : ∀ f g, r (f+g) ≤ r f+r g)
    (horth : ∀ f g, f*g = 0 → r (f+g) = r f+r g)
    (hsupport : ∀ f g, (∀ x, 0 < f x → 0 < g x) → r f ≤ r g)
    (hcuts : ∀ f, r f = ⨆ (ε : ℝ≥0) (_ : 0 < ε), r (continuousNNRealCut ε f))
    (f g : C(X, ℝ≥0)) :
    continuousDimensionIntegral r (f+g) = continuousDimensionIntegral r f + continuousDimensionIntegral r g := by
  rw [continuousDimensionIntegral_eq_lintegral r hfinite hmono hsub horth hsupport hcuts,
    continuousDimensionIntegral_eq_lintegral r hfinite hmono hsub horth hsupport hcuts,
    continuousDimensionIntegral_eq_lintegral r hfinite hmono hsub horth hsupport hcuts]
  simp only [ContinuousMap.add_apply,ENNReal.coe_add]
  exact lintegral_add_left (ENNReal.continuous_coe.comp f.continuous).measurable _

end Pureness
end

end OAI
