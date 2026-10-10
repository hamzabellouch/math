import OAI.Analysis.Pureness.Traces.DimensionContentRecovery
import Mathlib.MeasureTheory.Integral.Layercake

namespace OAI
noncomputable section
namespace CuntzPureness
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
  have h := lintegral_eq_lintegral_meas_lt μ (Filter.Eventually.of_forall (fun x => (f x).2)) hm.aemeasurable
  change (∫⁻ x, ENNReal.ofReal (f x) ∂μ) = ∫⁻ t in Ioi (0 : ℝ), μ {x | t < (f x : ℝ)} at h
  simp only [ENNReal.ofReal_coe_nnreal] at h
  rw [h]
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
end CuntzPureness

end

end OAI
