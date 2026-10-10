import OAI.Dynamics.StandardMap.RecenteredGraphs

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma product_slice_bound (E I : Set ℝ) (T : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ≥0∞)
    (K : ℝ≥0∞) (hE : MeasurableSet E) (_hI : MeasurableSet I) (hT : MeasurableSet T)
    (hsub : T ⊆ E ×ˢ I)
    (hslice : ∀ x ∈ E, ∫⁻ y in I, T.indicator f (x,y) ≤ K) :
    (∫⁻ z in T, f z) ≤ K*volume E := by
  have he : (∫⁻ z in T, f z) = ∫⁻ z in E ×ˢ I, T.indicator f z := by
    rw [lintegral_indicator hT,Measure.restrict_restrict hT,inter_eq_left.mpr hsub]
  rw [he]
  change (∫⁻ z, T.indicator f z ∂(volume.prod volume).restrict (E ×ˢ I)) ≤ _
  rw [← Measure.prod_restrict]
  calc
    _ ≤ ∫⁻ x in E, ∫⁻ y in I, T.indicator f (x,y) := lintegral_prod_le _
    _ ≤ ∫⁻ x in E, K := setLIntegral_mono' hE hslice
    _ = _ := by simp

lemma weighted_chart_product (E I : Set ℝ) (T A V : Set (ℝ × ℝ))
    (f : (ℝ × ℝ) → (ℝ × ℝ)) (D : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (g : ℝ × ℝ → ℝ≥0∞) (c C : ℝ) (K : ℝ≥0∞)
    (hE : MeasurableSet E) (hI : MeasurableSet I) (hT : MeasurableSet T)
    (hsub : T ⊆ E ×ˢ I) (hA : A ⊆ f '' T) (hV : f '' (E ×ˢ I) ⊆ V)
    (hD : ∀ z ∈ E ×ˢ I, HasFDerivWithinAt f (D z) (E ×ˢ I) z)
    (hinj : InjOn f (E ×ˢ I))
    (hlo : ∀ z ∈ E ×ˢ I, c ≤ |(D z).det|)
    (hhi : ∀ z ∈ E ×ˢ I, |(D z).det| ≤ C)
    (hslice : ∀ x ∈ E, ∫⁻ y in I, T.indicator (g ∘ f) (x,y) ≤ K) :
    (ENNReal.ofReal c*volume I)*(∫⁻ z in A, g z) ≤
      ENNReal.ofReal C*K*volume V := by
  have hw := (weighted_image_bounds volume T f D c C g hT
    (fun z hz => (hD z (hsub hz)).mono hsub) (hinj.mono hsub)
    (fun z hz => hlo z (hsub hz)) (fun z hz => hhi z (hsub hz))).2
  have hf : (∫⁻ z in A, g z) ≤ ENNReal.ofReal C*(K*volume E) :=
    (lintegral_mono_set hA).trans (hw.trans
      (mul_le_mul_of_nonneg_left (product_slice_bound E I T (g ∘ f) K hE hI hT hsub hslice) (by positivity)))
  have hl := (measure_image_bounds volume (E ×ˢ I) f D c C (hE.prod hI) hD hinj hlo hhi).1
  have hv : (ENNReal.ofReal c*volume I)*volume E ≤ volume V := by
    calc
      _ = ENNReal.ofReal c*volume (E ×ˢ I) := by
        change _ = ENNReal.ofReal c*(volume.prod volume) (E ×ˢ I)
        rw [Measure.prod_prod]
        ac_rfl
      _ ≤ volume (f '' (E ×ˢ I)) := hl
      _ ≤ volume V := measure_mono hV
  calc
    _ ≤ (ENNReal.ofReal c*volume I)*(ENNReal.ofReal C*(K*volume E)) := mul_le_mul_of_nonneg_left hf (by positivity)
    _ = (ENNReal.ofReal C*K)*((ENNReal.ofReal c*volume I)*volume E) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hv (by positivity)
end StandardMapEntropy

end OAI
