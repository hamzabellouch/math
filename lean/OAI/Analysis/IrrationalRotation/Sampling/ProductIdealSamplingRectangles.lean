import OAI.Analysis.IrrationalRotation.Sampling.ProductIdealSamplingProduct
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingCylinderWeights
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingTestIntegrability

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Invariant233.ProductModel.SamplingWeights

theorem rectangle_indicator_eq_product (D : Finset ℕ) (E F : ℕ → Set ℝ)
    (xy : EndpointPair) :
    (rectangle D E F).indicator (fun _ => (1 : ℝ)) xy =
      ∏ i : D, (E i).indicator (fun _ => (1 : ℝ)) (circleRepresentative (xy.1 i)) *
        (F i).indicator (fun _ => (1 : ℝ)) (circleRepresentative (xy.2 i)) := by
  classical
  have he (i : D) :
      (E i).indicator (fun _ => (1 : ℝ)) (circleRepresentative (xy.1 i)) *
      (F i).indicator (fun _ => (1 : ℝ)) (circleRepresentative (xy.2 i)) =
      if circleRepresentative (xy.1 i) ∈ E i ∧ circleRepresentative (xy.2 i) ∈ F i
        then 1 else 0 := by
    by_cases hE : circleRepresentative (xy.1 i) ∈ E i <;>
      by_cases hF : circleRepresentative (xy.2 i) ∈ F i <;> simp [hE, hF]
  simp_rw [he]
  rw [Finset.prod_ite_zero]
  simp [rectangle, Set.indicator_apply]

theorem integral_base_coordinate_product (D : Finset ℕ) (g : D → Circle → ℝ)
    (hg : ∀ i, Measurable (g i)) :
    (∫ x : Base, ∏ i : D, g i (x i) ∂baseMeasure) =
      ∏ i : D, ∫ x, g i x ∂circleMeasure := by
  have hr : MeasurePreserving D.restrict baseMeasure
      (Measure.pi (fun _ : D => circleMeasure)) :=
    ⟨by fun_prop, Measure.infinitePi_map_restrict _⟩
  have hm : Measurable (fun x : D → Circle => ∏ i : D, g i (x i)) := by
    apply Finset.measurable_prod
    intro i _
    exact (hg i).comp (measurable_pi_apply i)
  have he := integral_map (μ := baseMeasure) hr.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hr.map_eq] at he
  calc
    _ = ∫ x : D → Circle, ∏ i : D, g i (x i) ∂Measure.pi (fun _ : D => circleMeasure) := by
      simpa only [Finset.restrict] using he.symm
    _ = _ := integral_fintype_prod_eq_prod g

theorem idealLaw_real_rectangle_eq_integral {I D : Finset ℕ} (hID : I ⊆ D)
    {h α : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (hα : 0 < α)
    (E F : ℕ → Set ℝ) (hE : ∀ i ∈ D, MeasurableSet (E i))
    (hF : ∀ i ∈ D, MeasurableSet (F i)) :
    (IdealSampling.law I D h α).real (rectangle D E F) =
      ∫ x : Base, testedIdeal false D I h α E F x ∂baseMeasure := by
  unfold testedIdeal
  let G : D → Circle × Circle → ℝ := fun i p =>
    (E i).indicator (fun _ => (1 : ℝ)) (circleRepresentative p.1) *
      (F i).indicator (fun _ => (1 : ℝ)) (circleRepresentative p.2)
  have hG (i : D) : Measurable (G i) :=
    (((measurable_const.indicator (hE i i.property)).comp
      (Sampling.representative_measurable.comp measurable_fst)).mul
      ((measurable_const.indicator (hF i i.property)).comp
        (Sampling.representative_measurable.comp measurable_snd)))
  have hGb (i : D) (p : Circle × Circle) : ‖G i p‖ ≤ (1 : ℝ) := by
    dsimp [G]
    by_cases he : circleRepresentative p.1 ∈ E i <;>
      by_cases hf : circleRepresentative p.2 ∈ F i <;> simp [he, hf]
  have hk := IdealSampling.integral_law_product_eq_kernels hID hh0 hh1 hα G hG
    (fun _ => 1) (fun _ => zero_le_one) hGb
  rw [← integral_indicator_one (measurableSet_rectangle D E F hE hF)]
  change (∫ xy, (rectangle D E F).indicator (fun _ => (1 : ℝ)) xy
    ∂IdealSampling.law I D h α) = _
  simp_rw [rectangle_indicator_eq_product]
  change (∫ xy, ∏ i : D, G i (xy.1 i, xy.2 i) ∂IdealSampling.law I D h α) = _
  rw [hk]
  have hb := integral_base_coordinate_product D
    (fun i x => ∫ t in (0 : ℝ)..1, testedCoordinateWeight false I h α i (E i) (F i)
      (circleRepresentative x) t)
    (fun i => (stronglyMeasurable_testedAverage false I h α i (hE i i.property)
      (hF i i.property)).measurable.comp Sampling.representative_measurable)
  have hp (x : Base) : (∏ i : D, ∫ t in (0 : ℝ)..1,
      testedCoordinateWeight false I h α i (E i) (F i) (circleRepresentative (x i)) t) =
      ∏ i ∈ D, ∫ t in (0 : ℝ)..1,
      testedCoordinateWeight false I h α i (E i) (F i) (circleRepresentative (x i)) t := by
    rw [Finset.prod_coe_sort_eq_attach]
    exact Finset.prod_attach D (fun i => ∫ t in (0 : ℝ)..1,
      testedCoordinateWeight false I h α i (E i) (F i) (circleRepresentative (x i)) t)
  simp_rw [← hp]
  rw [hb]
  apply Finset.prod_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [] with x
  apply intervalIntegral.integral_congr
  intro t _
  simp only [G, IdealSampling.coordinateKernel, testedCoordinateWeight, coordinateWeight,
    Bool.false_eq_true, ite_false]
  rw [show circleRepresentative (x + (t : Circle)) =
      Int.fract (circleRepresentative x + t) from ProductCocycle.representative_add x t]
  ring

theorem idealLaw_real_cylinder_eq_integral {I D : Finset ℕ} (hID : I ⊆ D)
    {h α : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (hα : 0 < α)
    (t : SamplingCylinderWeak.CylinderTest (Bool × ℕ)) (hD : cylinderSupport t ⊆ D) :
    (IdealSampling.law I D h α).real (SamplingCylinderWeak.endpointCylinder t) =
      ∫ x : Base, testedIdeal false D I h α
        (cylinderCoordinateSet t false) (cylinderCoordinateSet t true) x ∂baseMeasure := by
  rw [endpointCylinder_eq_rectangle t D hD]
  exact idealLaw_real_rectangle_eq_integral hID hh0 hh1 hα _ _
    (fun i _ => measurableSet_cylinderCoordinateSet t false i)
    (fun i _ => measurableSet_cylinderCoordinateSet t true i)

end Invariant233.ProductModel.SamplingWeights

end

end OAI
