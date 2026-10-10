import OAI.MeasureTheory.Falconer.Recursion.SuffixDescriptors
import OAI.MeasureTheory.Falconer.Estimates.PositiveDistanceWeight

namespace OAI

namespace PlanarFalconer
open Set

theorem fine_cell_direction_dist (P Q : DyadicSquare)
    (hP : 0 < P.side) (hQ : 0 < Q.side) {a p : ℕ}
    (hp : P.side ≤ 1/(2:ℝ)^p) (hq : Q.side ≤ 1/(2:ℝ)^p)
    {x y x' y' : Plane} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier)
    (hx' : x' ∈ P.carrier) (hy' : y' ∈ Q.carrier)
    (hs : 96/(2:ℝ)^a ≤ dist x y) (hne : x' ≠ y') :
    dist (sourceRadialUnit y x) (sourceRadialUnit y' x') ≤ (2:ℝ)^a/(2:ℝ)^p := by
  have hdist : 0 < dist x y := (by positivity : 0 < 96/(2:ℝ)^a).trans_le hs
  have hxy : x ≠ y := dist_pos.mp hdist
  have hb := endpoint_direction_dist_le hxy hne
  rw [dist_comm y x] at hb
  have hxmove := P.dist_le hP.le hx hx'
  have hymove := Q.dist_le hQ.le hy hy'
  have hnum : 2*(dist y y'+dist x x') ≤ 8/(2:ℝ)^p := by
    calc
      _ ≤ 2*(2*Q.side+2*P.side) :=
        mul_le_mul_of_nonneg_left (add_le_add hymove hxmove) (by norm_num)
      _ ≤ 2*(2*(1/(2:ℝ)^p)+2*(1/(2:ℝ)^p)) := by gcongr
      _ = _ := by ring
  have hscale : 8/(2:ℝ)^p/(96/(2:ℝ)^a) ≤ (2:ℝ)^a/(2:ℝ)^p := by
    have hratio : 0 < (2:ℝ)^a/(2:ℝ)^p := by positivity
    have he : 8/(2:ℝ)^p/(96/(2:ℝ)^a) = ((2:ℝ)^a/(2:ℝ)^p)/12 := by field_simp; ring
    rw [he]
    linarith only [hratio]
  exact hb.trans ((div_le_div₀ (by positivity) hnum (by positivity) hs).trans hscale)

namespace PositiveDistanceData

theorem fine_endpoints_separated (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (hs : d.StronglySeparated) {P C : CellPath}
    (hP : P.take d.a = d.X) (hC : C.take d.a = d.Y)
    {x y : Plane} (hx : x ∈ (d.Q.descendant P).carrier)
    (hy : y ∈ (d.Q.descendant C).carrier) :
    96/(2:ℝ)^d.a ≤ dist x y := by
  have hh := (d.separated_distance_ratio hQ hs (z := (x,y))
    (hP ▸ d.Q.descendant_subset_take hQ P d.a hx)
    (hC ▸ d.Q.descendant_subset_take hQ C d.a hy)).1
  have hh' := (le_div_iff₀ (by positivity : 0 < (2:ℝ)^(-(d.a:ℝ)))).mp hh
  simpa only [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,div_eq_mul_inv] using hh'

theorem fine_directions (d : PositiveDistanceData) (hQ : d.Q.side = 1)
    (hs : d.StronglySeparated) {p : ℕ} {P C : CellPath}
    (hP : P.length = p) (hC : C.length = p)
    (hPX : P.take d.a = d.X) (hCY : C.take d.a = d.Y)
    {x y x' y' : Plane} (hx : x ∈ (d.Q.descendant P).carrier)
    (hy : y ∈ (d.Q.descendant C).carrier)
    (hx' : x' ∈ (d.Q.descendant P).carrier) (hy' : y' ∈ (d.Q.descendant C).carrier) :
    dist (sourceRadialUnit y x) (sourceRadialUnit y' x') ≤ (2:ℝ)^d.a/(2:ℝ)^p := by
  have hside : 0 < d.Q.side := by rw [hQ]; norm_num
  have hs' := d.fine_endpoints_separated hside hs hPX hCY hx' hy'
  exact fine_cell_direction_dist _ _ (d.Q.descendant_side_pos hside P)
    (d.Q.descendant_side_pos hside C)
    (by simp only [DyadicSquare.descendant_side,hQ,hP,le_refl])
    (by simp only [DyadicSquare.descendant_side,hQ,hC,le_refl]) hx hy hx' hy'
    (d.fine_endpoints_separated hside hs hPX hCY hx hy)
    (dist_pos.mp ((by positivity : 0 < 96/(2:ℝ)^d.a).trans_le hs'))

end PositiveDistanceData

end PlanarFalconer

end OAI
