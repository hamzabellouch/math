import OAI.Analysis.IrrationalRotation.Sampling.ProductIdealSamplingKernel
import Mathlib.MeasureTheory.Integral.Pi

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Invariant233.ProductModel.IdealSampling

def coordinateEndpoint (I : Finset ℕ) (h : ℝ) (i : ℕ) (p : Circle × Circle) :
    Circle × Circle :=
  (p.1, if i ∈ I then p.2 else p.1 +
    ((h * ScalarSampling.delta (circleRepresentative p.1) *
      circleRepresentative p.2 : ℝ) : Circle))

def coordinateEvent (I : Finset ℕ) (α : ℝ) (i : ℕ) : Set (Circle × Circle) :=
  if i ∈ I then {p | circleRepresentative p.1 < circleRepresentative p.2}
  else {p | α ≤ ScalarSampling.delta (circleRepresentative p.1)}

@[fun_prop] theorem coordinateEndpoint_measurable (I : Finset ℕ) (h : ℝ) (i : ℕ) :
    Measurable (coordinateEndpoint I h i) := by
  apply measurable_fst.prodMk
  by_cases hi : i ∈ I
  · simpa [coordinateEndpoint, hi] using measurable_snd
  · simp only [hi, ite_false]
    have hx : Measurable (fun p : Circle × Circle => circleRepresentative p.1) := by
      fun_prop
    have hz : Measurable (fun p : Circle × Circle => circleRepresentative p.2) := by
      fun_prop
    have hd : Measurable (fun p : Circle × Circle => ScalarSampling.delta (circleRepresentative p.1)) :=
      hx.min (measurable_const.sub hx)
    have hc : Continuous (fun r : ℝ => (r : Circle)) := by fun_prop
    exact measurable_fst.add (hc.measurable.comp ((measurable_const.mul hd).mul hz))

theorem coordinateEvent_measurable (I : Finset ℕ) (α : ℝ) (i : ℕ) :
    MeasurableSet (coordinateEvent I α i) := by
  by_cases hi : i ∈ I
  · simp only [coordinateEvent, hi, ite_true]
    exact measurableSet_lt (Sampling.representative_measurable.comp measurable_fst)
      (Sampling.representative_measurable.comp measurable_snd)
  · simp only [coordinateEvent, hi, ite_false]
    have hx := Sampling.representative_measurable.comp
      (measurable_fst : Measurable (Prod.fst : Circle × Circle → Circle))
    exact measurableSet_le measurable_const (hx.min (measurable_const.sub hx))

theorem mem_retained_iff {I D : Finset ℕ} (hID : I ⊆ D) (α : ℝ)
    (xz : EndpointPair) :
    xz ∈ triangularEvent I ∩ cutoffEvent I D α ↔
      ∀ i : D, (xz.1 i, xz.2 i) ∈ coordinateEvent I α i := by
  constructor
  · rintro ⟨ht, hc⟩ i
    by_cases hi : (i : ℕ) ∈ I
    · simpa [coordinateEvent, hi] using ht i hi
    · simpa [coordinateEvent, hi] using hc i (Finset.mem_sdiff.mpr ⟨i.property, hi⟩)
  · intro hall
    constructor
    · intro i hi
      simpa [coordinateEvent, hi] using hall ⟨i, hID hi⟩
    · intro i hi
      simpa [coordinateEvent, (Finset.mem_sdiff.mp hi).2] using
        hall ⟨i, (Finset.mem_sdiff.mp hi).1⟩

theorem retained_product_eq {I D : Finset ℕ} (hID : I ⊆ D) (h α : ℝ)
    (F : D → Circle × Circle → ℝ) (xz : EndpointPair) :
    (triangularEvent I ∩ cutoffEvent I D α).indicator
      (fun xz => ∏ i : D, F i (xz.1 i, endpoint I D h xz.1 xz.2 i)) xz =
      ∏ i : D, (coordinateEvent I α i).indicator
        (F i ∘ coordinateEndpoint I h i) (xz.1 i, xz.2 i) := by
  classical
  by_cases hx : xz ∈ triangularEvent I ∩ cutoffEvent I D α
  · rw [Set.indicator_of_mem hx]
    apply Finset.prod_congr rfl
    intro i _
    rw [Set.indicator_of_mem ((mem_retained_iff hID α xz).mp hx i)]
    simp [coordinateEndpoint, endpoint, i.property]
  · rw [Set.indicator_of_notMem hx]
    have hn : ¬ ∀ i : D, (xz.1 i, xz.2 i) ∈ coordinateEvent I α i :=
      fun hh => hx ((mem_retained_iff hID α xz).mpr hh)
    obtain ⟨i, hi⟩ := not_forall.mp hn
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Set.indicator_of_notMem hi _

theorem integral_law_product {I D : Finset ℕ} (hID : I ⊆ D) (h α : ℝ)
    (F : D → Circle × Circle → ℝ) (hF : ∀ i, Measurable (F i)) :
    (∫ xy, ∏ i : D, F i (xy.1 i, xy.2 i) ∂law I D h α) =
      ∏ i : D, ∫ p, (coordinateEvent I α i).indicator
        (F i ∘ coordinateEndpoint I h i) p ∂(circleMeasure.prod circleMeasure) := by
  classical
  let G : D → Circle × Circle → ℝ := fun i =>
    (coordinateEvent I α i).indicator (F i ∘ coordinateEndpoint I h i)
  have hG (i : D) : Measurable (G i) :=
    ((hF i).comp (coordinateEndpoint_measurable I h i)).indicator
      (coordinateEvent_measurable I α i)
  have htest : Measurable (fun xy : EndpointPair => ∏ i : D, F i (xy.1 i, xy.2 i)) := by
    apply Finset.measurable_prod
    intro i _
    exact (hF i).comp (((measurable_pi_apply (i : ℕ)).comp measurable_fst).prodMk
      ((measurable_pi_apply (i : ℕ)).comp measurable_snd))
  have hp : Measurable (fun p : D → Circle × Circle => ∏ i : D, G i (p i)) := by
    apply Finset.measurable_prod
    intro i _
    exact (hG i).comp (measurable_pi_apply i)
  rw [law, integral_map (endpointMap_measurable I D h).aemeasurable
    htest.aestronglyMeasurable]
  change (∫ xz, ∏ i : D, F i (xz.1 i, endpoint I D h xz.1 xz.2 i)
    ∂(sourceMeasure I).restrict (cutoffEvent I D α)) = _
  rw [sourceMeasure, Measure.restrict_restrict (cutoffEvent_measurable I D α),
    inter_comm, ← integral_indicator
      ((Sampling.triangularEvent_measurable I).inter (cutoffEvent_measurable I D α))]
  simp_rw [retained_product_eq hID h α F]
  have he := integral_map (μ := baseMeasure.prod baseMeasure)
    (measurePreserving_finite_coordinate_pairs D).measurable.aemeasurable
    hp.aestronglyMeasurable
  rw [(measurePreserving_finite_coordinate_pairs D).map_eq] at he
  change (∫ xz, ∏ i : D, G i (xz.1 i, xz.2 i) ∂baseMeasure.prod baseMeasure) = _
  rw [← he]
  exact integral_fintype_prod_eq_prod G

def coordinateKernel (I : Finset ℕ) (h α : ℝ) (i : ℕ) (s t : ℝ) : ℝ :=
  if i ∈ I then ScalarSampling.triangularKernel s t else ScalarSampling.rawKernel h α s t

theorem integral_coordinate_eq_kernel (I : Finset ℕ) {h α : ℝ}
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hα : 0 < α) (i : ℕ)
    (F : Circle × Circle → ℝ) (hF : Measurable F)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ p, ‖F p‖ ≤ C) :
    (∫ p, (coordinateEvent I α i).indicator (F ∘ coordinateEndpoint I h i) p
      ∂circleMeasure.prod circleMeasure) =
      ∫ x, (∫ t in (0 : ℝ)..1, coordinateKernel I h α i (circleRepresentative x) t *
        F (x, x + (t : Circle))) ∂circleMeasure := by
  have hm := (hF.comp (coordinateEndpoint_measurable I h i)).indicator
    (coordinateEvent_measurable I α i)
  have hint : Integrable ((coordinateEvent I α i).indicator
      (F ∘ coordinateEndpoint I h i)) (circleMeasure.prod circleMeasure) := by
    apply (integrable_const C).mono' hm.aestronglyMeasurable
    filter_upwards [] with p
    by_cases hp : p ∈ coordinateEvent I α i
    · simpa [Set.indicator_of_mem hp] using hbound (coordinateEndpoint I h i p)
    · simp [Set.indicator_of_notMem hp, hC]
  rw [integral_prod _ hint]
  apply integral_congr_ae
  filter_upwards [] with x
  have hfx : Measurable (fun z : Circle => F (x, z)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  by_cases hi : i ∈ I
  · simpa [coordinateEvent, coordinateEndpoint, coordinateKernel, hi,
      Set.indicator, Function.comp_def] using
      integral_triangular_endpoint_eq_kernel x (fun z => F (x, z)) hfx
  · have he := integral_cutoff_displacement_eq_rawKernel hh0 hh1 hα
      x (fun z => F (x, z)) hfx
    by_cases hc : α ≤ ScalarSampling.delta (circleRepresentative x)
    · simpa [coordinateEvent, coordinateEndpoint, coordinateKernel, hi, hc,
        Set.indicator, Function.comp_def] using he
    · simpa [coordinateEvent, coordinateEndpoint, coordinateKernel, hi, hc,
        Set.indicator, Function.comp_def] using he

theorem integral_law_product_eq_kernels {I D : Finset ℕ} (hID : I ⊆ D)
    {h α : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (hα : 0 < α)
    (F : D → Circle × Circle → ℝ) (hF : ∀ i, Measurable (F i))
    (C : D → ℝ) (hC : ∀ i, 0 ≤ C i) (hbound : ∀ i p, ‖F i p‖ ≤ C i) :
    (∫ xy, ∏ i : D, F i (xy.1 i, xy.2 i) ∂law I D h α) =
      ∏ i : D, ∫ x, (∫ t in (0 : ℝ)..1,
        coordinateKernel I h α i (circleRepresentative x) t *
          F i (x, x + (t : Circle))) ∂circleMeasure := by
  rw [integral_law_product hID h α F hF]
  apply Finset.prod_congr rfl
  intro i _
  exact integral_coordinate_eq_kernel I hh0 hh1 hα i (F i) (hF i) (hC i) (hbound i)

end Invariant233.ProductModel.IdealSampling

end

end OAI
