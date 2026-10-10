import OAI.MeasureTheory.Falconer.Radial.RadialPreparation
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology

abbrev UnitCircle := {z : Plane // ‖z‖ = 1}

theorem disjoint_sub_ne_zero {A B : Set Plane} (hAB : Disjoint A B)
    (x : A) (y : B) : (y : Plane) - x ≠ 0 := by
  intro h
  have he := sub_eq_zero.mp h
  exact Set.disjoint_left.mp hAB x.property (he ▸ y.property)

noncomputable def radialOn {A B : Set Plane} (hAB : Disjoint A B)
    (x : A) (y : B) : UnitCircle :=
  ⟨‖(y : Plane)-x‖⁻¹ • ((y : Plane)-x), norm_smul_inv_norm (disjoint_sub_ne_zero hAB x y)⟩

theorem continuous_radialOn {A B : Set Plane} (hAB : Disjoint A B) :
    Continuous (fun z : A × B => radialOn hAB z.1 z.2) := by
  have hd : Continuous (fun z : A × B => (z.2 : Plane)-(z.1 : Plane)) :=
    (continuous_subtype_val.comp continuous_snd).sub
      (continuous_subtype_val.comp continuous_fst)
  apply Continuous.subtype_mk
  exact (hd.norm.inv₀ (fun z => norm_ne_zero_iff.mpr (disjoint_sub_ne_zero hAB z.1 z.2))).smul hd

theorem continuous_radialOn_source {A B : Set Plane} (hAB : Disjoint A B) (x : A) :
    Continuous (radialOn hAB x) := by
  exact (continuous_radialOn hAB).comp (f := fun point : B => (x, point))
    (Continuous.prodMk_right x)

theorem continuous_radialOn_center {A B : Set Plane} (hAB : Disjoint A B) (y : B) :
    Continuous (fun x : A => radialOn hAB x y) := by
  exact (continuous_radialOn hAB).comp (f := fun point : A => (point, y))
    (Continuous.prodMk_left y)

noncomputable def radialProbability {A B : Set Plane} (hAB : Disjoint A B)
    (μ : ProbabilityMeasure B) (x : A) : ProbabilityMeasure UnitCircle :=
  μ.map (radialOn hAB x)

theorem continuous_radialProbability {A B : Set Plane} (hAB : Disjoint A B)
    (μ : ProbabilityMeasure B) : Continuous (radialProbability hAB μ) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  have hi : Continuous (fun x : A => ∫ y : B, f (radialOn hAB x y) ∂μ) := by
    apply continuous_of_dominated (bound := fun _ : B => ‖f‖)
    · intro x
      exact (f.continuous.comp (continuous_radialOn_source hAB x)).aestronglyMeasurable
    · intro x
      exact Filter.Eventually.of_forall (fun y => f.norm_coe_le_norm _)
    · exact integrable_const _
    · exact Filter.Eventually.of_forall (fun y =>
        f.continuous.comp (continuous_radialOn_center hAB y))
  have he (x : A) : (∫ z, f z ∂(radialProbability hAB μ x)) =
      ∫ y : B, f (radialOn hAB x y) ∂μ := by
    change (∫ z, f z ∂((μ : Measure B).map (radialOn hAB x))) = _
    exact integral_map (continuous_radialOn_source hAB x).measurable.aemeasurable
      f.continuous.aestronglyMeasurable
  simpa only [he] using hi

theorem continuous_radial_source_measure {A B : Set Plane} (hAB : Disjoint A B) (x : A) :
    Continuous (fun μ : ProbabilityMeasure B => radialProbability hAB μ x) :=
  ProbabilityMeasure.continuous_map (continuous_radialOn_source hAB x)

end PlanarFalconer

end OAI
