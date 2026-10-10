import OAI.Dynamics.StandardMap.LiftEventMeasure

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma scaled_weighted_chart_product (E I : Set ℝ) (T A V : Set (ℝ × ℝ))
    (f : (ℝ × ℝ) → (ℝ × ℝ)) (D : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (g : ℝ × ℝ → ℝ≥0∞) (c C : ℝ) (d K : ℝ≥0∞) (hd : d ≠ ∞)
    (hE : MeasurableSet E) (hI : MeasurableSet I) (hT : MeasurableSet T)
    (hsub : T ⊆ E ×ˢ I) (hA : A ⊆ f '' T) (hV : f '' (E ×ˢ I) ⊆ V)
    (hD : ∀ z ∈ E ×ˢ I, HasFDerivWithinAt f (D z) (E ×ˢ I) z)
    (hinj : InjOn f (E ×ˢ I))
    (hlo : ∀ z ∈ E ×ˢ I, c ≤ |(D z).det|)
    (hhi : ∀ z ∈ E ×ˢ I, |(D z).det| ≤ C)
    (hslice : ∀ x ∈ E, d*(∫⁻ y in I, T.indicator (g ∘ f) (x,y)) ≤ K) :
    (ENNReal.ofReal c*volume I)*d*(∫⁻ z in A, g z) ≤
      ENNReal.ofReal C*K*volume V := by
  have hw := (weighted_image_bounds volume T f D c C g hT
    (fun z hz => (hD z (hsub hz)).mono hsub) (hinj.mono hsub)
    (fun z hz => hlo z (hsub hz)) (fun z hz => hhi z (hsub hz))).2
  have hf : d*(∫⁻ z in A, g z) ≤ ENNReal.ofReal C*(K*volume E) := by
    calc
      _ ≤ d*(ENNReal.ofReal C*(∫⁻ z in T, g (f z))) :=
        mul_le_mul_of_nonneg_left ((lintegral_mono_set hA).trans hw) (by positivity)
      _ = ENNReal.ofReal C*(d*(∫⁻ z in T, g (f z))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (scaled_product_slice_bound E I T (g ∘ f) d K hd hE hI hT hsub hslice) (by positivity)
  have hl := (measure_image_bounds volume (E ×ˢ I) f D c C (hE.prod hI) hD hinj hlo hhi).1
  have hv : (ENNReal.ofReal c*volume I)*volume E ≤ volume V := by
    calc
      _ = ENNReal.ofReal c*volume (E ×ˢ I) := by
        change _ = ENNReal.ofReal c*(volume.prod volume) (E ×ˢ I)
        rw [Measure.prod_prod]; ac_rfl
      _ ≤ volume (f '' (E ×ˢ I)) := hl
      _ ≤ volume V := measure_mono hV
  calc
    _ = (ENNReal.ofReal c*volume I)*(d*(∫⁻ z in A, g z)) := by ring
    _ ≤ (ENNReal.ofReal c*volume I)*(ENNReal.ofReal C*(K*volume E)) := mul_le_mul_of_nonneg_left hf (by positivity)
    _ = (ENNReal.ofReal C*K)*((ENNReal.ofReal c*volume I)*volume E) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hv (by positivity)
end StandardMapEntropy

end OAI
