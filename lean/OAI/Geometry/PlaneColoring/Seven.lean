import OAI.Geometry.PlaneColoring.Assembly
import OAI.Geometry.PlaneColoring.Lattice
import OAI.Geometry.PlaneColoring.Metric
import OAI.Geometry.PlaneColoring.Covering
import OAI.Geometry.PlaneColoring.MeasurableAssembly
import OAI.Geometry.PlaneColoring.MeasurableProper

namespace OAI

noncomputable section

namespace Problem160

/-- The elementary covering-radius statement is the only geometric input
needed to turn the index-seven lattice coloring into a plane coloring. -/
theorem properColoring_seven_of_normalized_cover
    (hcover : ∀ x y : ℝ, ∃ a b : ℤ,
      (x - ((a : ℝ) + (b : ℝ) / 2)) ^ 2 +
        (y - Real.sqrt 3 * b / 2) ^ 2 ≤ (1 / 3 : ℝ)) :
    ProperColoring 7 := by
  apply exists_unit_distance_coloring_of_center_cover
    (fun p : ℤ × ℤ => triangularLattice p.1 p.2)
    (fun p : ℤ × ℤ => SevenLattice.colorFin p.1 p.2) (7 / 15 : ℝ)
  · intro x
    obtain ⟨a, b, hab⟩ := hcover ((5 / 4 : ℝ) * x 0) ((5 / 4 : ℝ) * x 1)
    exact ⟨(a, b), dist_triangularLattice_le_of_coordinates x a b hab⟩
  · norm_num
  · intro i j hij hc
    have hq := SevenLattice.same_color_separation
      (SevenLattice.colorFin_injective_value hc) hij
    have hsep := triangularLattice_dist_gt_two i.1 i.2 j.1 j.2 hq
    linarith

/-- The classical seven-color upper bound, with all boundary points assigned
using the closed triangular-lattice cover. -/
theorem properColoring_seven : ProperColoring 7 :=
  properColoring_seven_of_normalized_cover triangular_lattice_cover

/-- The seven-color construction admits a measurable choice on its boundary
points: select the first covering center in a countable enumeration. -/
theorem exists_measurable_proper_seven :
    ∃ c : Plane → Fin 7, Measurable c ∧
      ∀ x y : Plane, dist x y = 1 → c x ≠ c y := by
  apply exists_measurable_unit_distance_coloring_of_center_cover
    (fun p : ℤ × ℤ => triangularLattice p.1 p.2)
    (fun p : ℤ × ℤ => SevenLattice.colorFin p.1 p.2) (7 / 15 : ℝ)
  · intro x
    obtain ⟨a, b, hab⟩ := triangular_lattice_cover
      ((5 / 4 : ℝ) * x 0) ((5 / 4 : ℝ) * x 1)
    exact ⟨(a, b), dist_triangularLattice_le_of_coordinates x a b hab⟩
  · norm_num
  · intro i j hij hc
    have hq := SevenLattice.same_color_separation
      (SevenLattice.colorFin_injective_value hc) hij
    have hsep := triangularLattice_dist_gt_two i.1 i.2 j.1 j.2 hq
    linarith

/-- The classical measurable seven-color construction satisfies the exact
weak pair-measure condition. -/
theorem weakMeasurableColoring_seven : WeakMeasurableColoring 7 := by
  obtain ⟨c, hc, hproper⟩ := exists_measurable_proper_seven
  exact weakMeasurableColoring_of_aemeasurable_proper c hc.aemeasurable hproper

end Problem160

end

end OAI
