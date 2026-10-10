import OAI.Analysis.IrrationalRotation.Model.ProductSampling
import OAI.Analysis.IrrationalRotation.Analysis.TriangularProbability
import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace Invariant233.ProductModel

private theorem rep_measurable : Measurable circleRepresentative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable

private theorem rep_injective : Function.Injective circleRepresentative :=
  Subtype.val_injective.comp (AddCircle.equivIco (1 : ℝ) 0).injective

theorem circle_strict_triangle_mass :
    (circleMeasure.prod circleMeasure)
      {xz : Circle × Circle | circleRepresentative xz.1 < circleRepresentative xz.2} =
        (1 / 2 : ℝ≥0∞) := by
  let ν := circleMeasure.map circleRepresentative
  have : NullSingletonClass circleMeasure := by
    change NullSingletonClass (volume : Measure Circle)
    constructor
    intro x
    simpa using (AddCircle.volume_closedBall (T := (1 : ℝ)) (x := x) 0)
  have : IsProbabilityMeasure ν := inferInstance
  have : NullSingletonClass ν := by
    constructor
    intro x
    change (circleMeasure.map circleRepresentative) {x} = 0
    rw [map_apply rep_measurable (measurableSet_singleton x)]
    apply Set.Subsingleton.measure_zero
    intro a ha b hb
    apply rep_injective
    exact ha.trans hb.symm
  have hmass := InvariantProjection.TriangularProbability.measure_strict_triangle ν
  change ((circleMeasure.map circleRepresentative).prod
    (circleMeasure.map circleRepresentative)) _ = _ at hmass
  have hm : Measurable (Prod.map circleRepresentative circleRepresentative) :=
    rep_measurable.prodMap rep_measurable
  rw [map_prod_map circleMeasure circleMeasure rep_measurable rep_measurable,
    map_apply hm (measurableSet_lt measurable_fst measurable_snd)] at hmass
  exact hmass

theorem measurePreserving_finite_coordinate_pairs (I : Finset ℕ) :
    MeasurePreserving
      (fun xz : EndpointPair => fun i : I => (xz.1 i, xz.2 i))
      (baseMeasure.prod baseMeasure)
      (Measure.pi (fun _ : I => circleMeasure.prod circleMeasure)) := by
  have hr : MeasurePreserving I.restrict baseMeasure
      (Measure.pi (fun _ : I => circleMeasure)) := by
    refine ⟨Finset.measurable_restrict I, ?_⟩
    exact infinitePi_map_restrict (fun _ : ℕ => circleMeasure)
  let e := MeasurableEquiv.arrowProdEquivProdArrow Circle Circle I
  have he := (measurePreserving_arrowProdEquivProdArrow Circle Circle I
    (fun _ => circleMeasure) (fun _ => circleMeasure)).symm
  exact he.comp (hr.prod hr)

theorem triangularEvent_mass (I : Finset ℕ) :
    (baseMeasure.prod baseMeasure) (triangularEvent I) = (1 / 2 : ℝ≥0∞) ^ I.card := by
  let E : Set (Circle × Circle) :=
    {xz | circleRepresentative xz.1 < circleRepresentative xz.2}
  have hE : MeasurableSet E :=
    measurableSet_lt (rep_measurable.comp measurable_fst) (rep_measurable.comp measurable_snd)
  have hpre : triangularEvent I =
      (fun xz : EndpointPair => fun i : I => (xz.1 i, xz.2 i)) ⁻¹'
        Set.univ.pi (fun _ : I => E) := by
    ext xz
    simp [triangularEvent, E, Set.mem_pi]
  rw [hpre, (measurePreserving_finite_coordinate_pairs I).measure_preimage
    (MeasurableSet.univ_pi (fun _ => hE)).nullMeasurableSet, Measure.pi_pi]
  simp only [E, circle_strict_triangle_mass, Finset.prod_const, Finset.card_univ,
    Fintype.card_coe]

private theorem replacement_measurable (I : Finset ℕ) :
    Measurable (fun xz : EndpointPair => (xz.1, selectedEndpoint I xz.1 xz.2)) := by
  refine measurable_fst.prodMk (Measurable.of_eval fun index => ?_)
  by_cases hi : index ∈ I
  · simpa [selectedEndpoint, hi, Function.comp_def] using
      (measurable_pi_apply index).comp measurable_snd
  · simpa [selectedEndpoint, hi, Function.comp_def] using
      (measurable_pi_apply index).comp measurable_fst

theorem triangularLaw_mass (I : Finset ℕ) :
    triangularLaw I Set.univ = (1 / 2 : ℝ≥0∞) ^ I.card := by
  rw [triangularLaw, map_apply (replacement_measurable I) MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply_univ]
  exact triangularEvent_mass I

end Invariant233.ProductModel

end

end OAI
