import OAI.Analysis.IrrationalRotation.Model.ProductBase
import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.ProductModel.OrderedRigidity

theorem representative_injective : Function.Injective circleRepresentative := by
  intro x y h
  apply (AddCircle.equivIco (1 : ℝ) 0).injective
  exact Subtype.ext h

theorem representative_measurable : Measurable circleRepresentative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable

theorem representative_bounds (x : Circle) :
    0 ≤ circleRepresentative x ∧ circleRepresentative x < 1 := by
  simpa [circleRepresentative] using (AddCircle.equivIco (1 : ℝ) 0 x).property

theorem coordinate_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → Base}
    (hf : Measurable f) (i : ℕ) :
    Integrable (fun ω => circleRepresentative (f ω i)) μ := by
  apply Integrable.of_bound
    ((representative_measurable.comp ((measurable_pi_apply i).comp hf)).aestronglyMeasurable)
    1
  exact Filter.Eventually.of_forall fun ω => by
    change ‖circleRepresentative (f ω i)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (representative_bounds (f ω i)).1]
    exact (representative_bounds (f ω i)).2.le

theorem ae_eq_of_ordered_equal_marginals
    (η : Measure (Base × Base)) [IsFiniteMeasure η]
    (hmarg : η.map Prod.fst = η.map Prod.snd)
    (horder : ∀ᵐ xy ∂η, Ordered xy.1 xy.2) :
    ∀ᵐ xy ∂η, xy.1 = xy.2 := by
  have hcoord (i : ℕ) :
      (fun xy : Base × Base => circleRepresentative (xy.1 i)) =ᵐ[η]
        fun xy => circleRepresentative (xy.2 i) := by
    apply (integral_eq_iff_of_ae_le
      (coordinate_integrable measurable_fst i)
      (coordinate_integrable measurable_snd i)
      (horder.mono fun xy hxy => hxy i)).1
    let g : Base → ℝ := fun x => circleRepresentative (x i)
    have hg : StronglyMeasurable g :=
      (representative_measurable.comp (measurable_pi_apply i)).stronglyMeasurable
    calc
      (∫ xy, circleRepresentative (xy.1 i) ∂η) = ∫ x, g x ∂η.map Prod.fst :=
        (integral_map_of_stronglyMeasurable measurable_fst hg).symm
      _ = ∫ x, g x ∂η.map Prod.snd := by rw [hmarg]
      _ = ∫ xy, circleRepresentative (xy.2 i) ∂η :=
        integral_map_of_stronglyMeasurable measurable_snd hg
  filter_upwards [ae_all_iff.2 hcoord] with xy hxy
  funext i
  exact representative_injective (hxy i)

theorem eq_diagonal_of_ordered_equal_marginals
    (η : Measure (Base × Base)) [IsFiniteMeasure η]
    (hmarg : η.map Prod.fst = η.map Prod.snd)
    (horder : ∀ᵐ xy ∂η, Ordered xy.1 xy.2) :
    η = (η.map Prod.fst).map (fun x : Base => (x, x)) := by
  rw [Measure.map_map (show Measurable (fun x : Base => (x, x)) from
    measurable_id.prodMk measurable_id) measurable_fst]
  calc
    η = η.map id := Measure.map_id.symm
    _ = η.map ((fun x : Base => (x, x)) ∘ Prod.fst) := by
      apply Measure.map_congr
      filter_upwards [ae_eq_of_ordered_equal_marginals η hmarg horder] with xy hxy
      exact Prod.ext rfl hxy.symm

theorem eq_diagonal_haar_of_ordered
    (η : Measure (Base × Base))
    (hfst : η.map Prod.fst = baseMeasure)
    (hsnd : η.map Prod.snd = baseMeasure)
    (horder : ∀ᵐ xy ∂η, Ordered xy.1 xy.2) :
    η = baseMeasure.map (fun x : Base => (x, x)) := by
  have : IsProbabilityMeasure (η.map Prod.fst) := hfst ▸ baseMeasure_probability
  have : IsProbabilityMeasure η :=
    Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable
  simpa [hfst] using eq_diagonal_of_ordered_equal_marginals η
    (hfst.trans hsnd.symm) horder

end Invariant233.ProductModel.OrderedRigidity

end

end OAI
