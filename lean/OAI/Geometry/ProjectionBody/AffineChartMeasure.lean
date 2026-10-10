import OAI.Geometry.ProjectionBody.NullHyperplane
import Mathlib.Analysis.InnerProductSpace.NormDet

namespace OAI

noncomputable section
open Set MeasureTheory Measure

namespace ProjectionCounterexample

variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The volume of a projected affine chart, with its genuine linear Jacobian. -/
theorem measure_projected_affine_chart (L : U →ₗ[ℝ] V) (c : V)
    (q : V →ₗ[ℝ] V) (s : Set U) :
    μHE[Module.finrank ℝ U] (q '' ((fun x => c + L x) '' s)) =
      ENNReal.ofReal (q.comp L).normDet * volume s := by
  have himage : q '' ((fun x => c + L x) '' s) =
      (fun y => q c + y) '' (q.comp L '' s) := by
    simp only [Set.image_image]
    congr 1
    funext x
    exact map_add q c (L x)
  rw [himage, (isometry_add_left _).euclideanHausdorffMeasure_image,
    (q.comp L).euclideanHausdorffMeasure_image_eq_normDet_mul_volume]

/-- Intersecting a facet chart with a genuinely transverse affine equation
has zero facet-dimensional measure, including after any linear projection. -/
theorem measure_projected_transverse_intersection (L : U →ₗ[ℝ] V) (c : V)
    (q : V →ₗ[ℝ] V) (g : V →ₗ[ℝ] ℝ) (r : ℝ) (S T : Set V)
    (hS : S ⊆ (fun x => c + L x) '' (univ : Set U))
    (hT : T ⊆ {y | g y = r}) (hg : g.comp L ≠ 0) :
    μHE[Module.finrank ℝ U] (q '' (S ∩ T)) = 0 := by
  have hsub : q '' (S ∩ T) ⊆
      q '' ((fun x => c + L x) '' {x | (g.comp L) x = r - g c}) := by
    rintro z ⟨y, ⟨hyS, hyT⟩, rfl⟩
    obtain ⟨x, _, rfl⟩ := hS hyS
    refine ⟨c + L x, ⟨x, ?_, rfl⟩, rfl⟩
    have heq := hT hyT
    change g (c + L x) = r at heq
    rw [map_add] at heq
    change g (L x) = r - g c
    exact eq_sub_of_add_eq' heq
  apply measure_mono_null hsub
  rw [measure_projected_affine_chart,
    volume_linear_level_eq_zero (g.comp L) hg, mul_zero]

end ProjectionCounterexample

end

end OAI
