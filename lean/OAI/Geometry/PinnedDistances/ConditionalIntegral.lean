import OAI.Geometry.PinnedDistances.FiniteLaw

namespace OAI

universe u1 u2 u3 u4 u5

section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace WeakPinned.Bounded

lemma integrable_one_bound {X : Type u1} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (hbound : ∀ x,‖f x‖≤1) : Integrable f μ := by
  exact (integrable_const (1:ℝ)).mono' hf.aestronglyMeasurable (Eventually.of_forall hbound)

variable {Ω : Type u2} {E : Type u3} {X : Type u4} {Y : Type u5} [MeasurableSpace Ω] [MeasurableSpace E]
  [MeasurableSpace X] [MeasurableSpace Y]

lemma integral_fiber_indicator (Q : Measure E) (μ : Measure X)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure μ]
    (f : E × X → ℝ) (hf : Measurable f) (hbound : ∀ p,‖f p‖≤1)
    (s : Set E) (hs : MeasurableSet s) :
    (∫ e in s, ∫ x,f (e,x) ∂ μ ∂ Q)=
      ∫ p,(s ×ˢ Set.univ).indicator f p ∂ Q.prod μ := by
  have hi := integrable_one_bound (Q.prod μ) f hf hbound
  rw [integral_prod _ (hi.indicator (hs.prod MeasurableSet.univ))]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [] with e
  by_cases he : e∈s
  · simp [Set.indicator_of_mem,he]
  · simp [Set.indicator_of_notMem,he]

lemma conditional_integral_eq
    (R : Measure Ω) (Q : Measure E) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure R] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (e : Ω → E) (z : Ω → X) (w : Ω → Y)
    (he : Measurable e) (hz : Measurable z) (hw : Measurable w)
    (hmz : R.map (fun r => (e r,z r))=Q.prod μ)
    (hmw : R.map (fun r => (e r,w r))=Q.prod ν)
    (f : E × X → ℝ) (g : E × Y → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ p,‖f p‖≤1) (hgb : ∀ p,‖g p‖≤1)
    (heq : ∀ᵐ r ∂ R,f (e r,z r)=g (e r,w r)) :
    ∀ᵐ a ∂ Q,(∫ x,f (a,x) ∂ μ)=(∫ y,g (a,y) ∂ ν) := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq
  · exact (integrable_one_bound (Q.prod μ) f hf hfb).integral_prod_left
  · exact (integrable_one_bound (Q.prod ν) g hg hgb).integral_prod_left
  · intro s hs _
    rw [integral_fiber_indicator Q μ f hf hfb s hs,
      integral_fiber_indicator Q ν g hg hgb s hs,← hmz,← hmw]
    rw [integral_map_of_stronglyMeasurable (he.prodMk hz)
      (hf.indicator (hs.prod MeasurableSet.univ)).stronglyMeasurable,
      integral_map_of_stronglyMeasurable (he.prodMk hw)
      (hg.indicator (hs.prod MeasurableSet.univ)).stronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [heq] with r hr
    by_cases h : e r∈s <;> simp [h,hr]

end WeakPinned.Bounded

end
end

end OAI
