import OAI.MeasureTheory.Falconer.Fourier.ChartSymbolControl

namespace OAI

/-! # Borel spatial restrictions preserve the angular symbol bounds

This permits the finite coarse-filter product pieces to enter the same
graph estimate as dyadic cells. Only angular derivatives occur there.
-/
namespace Falconer
open Set MeasureTheory
open scoped ContDiff
attribute [local instance] Classical.propDecidable

noncomputable def spatialRestrictionSymbol {d : ℕ} (S : Set (Space d))
    (b : Space d → Sphere d → ℂ) (x : Space d) (w : Sphere d) : ℂ :=
  if x ∈ S then b x w else 0

theorem spatialRestrictionSymbol_measurable {d : ℕ} (S : Set (Space d))
    (hS : MeasurableSet S) (b : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) :
    Measurable (Function.uncurry (spatialRestrictionSymbol S b)) :=
  hb.ite (hS.preimage measurable_fst) measurable_const

theorem endpointTransform_spatialRestrictionSymbol {d : ℕ} (S : Set (Space d))
    (hS : MeasurableSet S) (μ : Measure (Space d)) (M : ℝ)
    (b : Space d → Sphere d → ℂ) (r : ℝ) (w : Sphere d) :
    endpointTransform μ M (spatialRestrictionSymbol S b) r w =
      endpointTransform (μ.restrict S) M b r w := by
  unfold endpointTransform
  congr 1
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ S <;> simp [spatialRestrictionSymbol,hx]

theorem ChartSymbolControl.spatialRestriction {n m : ℕ}
    {b : Space (n+2) → Sphere (n+2) → ℂ} {B D : ℝ}
    (h : ChartSymbolControl m b B D) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (S : Set (Space (n+2))) (hS : MeasurableSet S) :
    ChartSymbolControl m (spatialRestrictionSymbol S b) B D := by
  refine ⟨spatialRestrictionSymbol_measurable S hS b h.measurable,?_,?_,?_⟩
  · intro x w
    by_cases hx : x ∈ S
    · simpa only [spatialRestrictionSymbol,ite_eq_left hx] using h.bound x w
    · simpa only [spatialRestrictionSymbol,ite_eq_right hx,norm_zero] using hB
  · intro x e y
    by_cases hx : x ∈ S
    · have he : spatialRestrictionSymbol S b x = b x := by
        funext w; simp only [spatialRestrictionSymbol,ite_eq_left hx]
      rw [he]
      exact h.smooth x e y
    · have he : spatialRestrictionSymbol S b x = fun _ => 0 := by
        funext w; simp only [spatialRestrictionSymbol,ite_eq_right hx]
      rw [he]
      exact contDiff_const
  · intro e k hk x y hy u hu
    by_cases hx : x ∈ S
    · have he : spatialRestrictionSymbol S b x = b x := by
        funext w; simp only [spatialRestrictionSymbol,ite_eq_left hx]
      rw [he]
      exact h.derivative e k hk x y hy u hu
    · have he : spatialRestrictionSymbol S b x = fun _ => 0 := by
        funext w; simp only [spatialRestrictionSymbol,ite_eq_right hx]
      rw [he]
      have hzero : rotatedChartAmplitude e (fun _ => (0 : ℂ)) y = fun _ => 0 := rfl
      rw [hzero]
      simp only [iteratedDeriv_const,ite_self,norm_zero]
      exact mul_nonneg hB (pow_nonneg hD k)

end Falconer

end OAI
