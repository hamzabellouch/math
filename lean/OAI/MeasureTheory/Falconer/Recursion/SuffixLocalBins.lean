import OAI.MeasureTheory.Falconer.Graphs.LocalDistanceCollision
import OAI.MeasureTheory.Falconer.Recursion.SuffixDistanceTaylor
import OAI.MeasureTheory.Falconer.Geometry.PositiveDistanceBins

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem bin_sq_le_unrestricted_collision (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    (binL2Norm d.distance d.width)^2 ≤
      (d.cellPair.prod d.cellPair) {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ d.width} := by
  rw [pow_two,binL2Norm_mul_self]
  apply (real_bin_collision_bound d.distance d.width_pos).trans
  rw [d.distance_collision]
  exact Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self _

theorem suffix_local_bin_sq (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : d.Q.side = 1) (hs : d.StronglySeparated) {p : ℕ} (hst : d.a+d.t ≤ 2*p)
    {P C : CellPath} (hP : P.length = p) (hC : C.length = p)
    (hPX : P.take d.a = d.X) (hCY : C.take d.a = d.Y) {H : ℝ≥0∞}
    (hproj : ((d.ρ.restrict (d.Q.descendant C).carrier).prod (d.ρ.restrict (d.Q.descendant C).carrier))
      {z : Plane × Plane | |planeDot (z.1-z.2)
        (sourceRadialUnit (d.Q.descendant C).center (d.Q.descendant P).center : Plane)| ≤
          1/(2:ℝ)^d.t} ≤ H) :
    (binL2Norm ({d with X := P,Y := C} : PositiveDistanceData).distance d.width)^2 ≤
      (d.ρ (d.Q.descendant P).carrier)^2 * (((bandOffsets 3).card : ℝ≥0∞)*H) := by
  have hw : d.width = 1/(2:ℝ)^d.t := by
    simp only [width,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
  apply (bin_sq_le_unrestricted_collision ({d with X := P,Y := C} : PositiveDistanceData)).trans
  simpa only [cellPair,width,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
    using local_distance_collision_bound d.ρ (d.Q.descendant P) (d.Q.descendant C) _
      (by positivity : 0 < 1/(2:ℝ)^d.t)
      (fun x hx y hy => d.suffix_distance_affine hQ hs hst hP hC hPX hCY hx hy) hproj

end PositiveDistanceData

end PlanarFalconer

end OAI
