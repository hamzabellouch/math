import OAI.MeasureTheory.Falconer.Measures.NormAffineRemainder
import OAI.MeasureTheory.Falconer.Recursion.SuffixDirectionGeometry

namespace OAI

namespace PlanarFalconer
open Set

theorem fine_distance_affine_error (P Q : DyadicSquare)
    (hP : 0 < P.side) (hQ : 0 < Q.side) {a p t : ℕ}
    (hp : P.side ≤ 1/(2:ℝ)^p) (hq : Q.side ≤ 1/(2:ℝ)^p)
    (hs : 96/(2:ℝ)^a ≤ dist P.center Q.center) (hst : a+t ≤ 2*p)
    {x y : Plane} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) :
    |dist x y-planeDot (x-y) (sourceRadialUnit Q.center P.center : Plane)| ≤ 1/(2:ℝ)^t := by
  have hdist : 0 < dist P.center Q.center := (by positivity : 0 < 96/(2:ℝ)^a).trans_le hs
  have hc : P.center ≠ Q.center := dist_pos.mp hdist
  have hraw := norm_affine_remainder (x-y) (P.center-Q.center) (sub_ne_zero.mpr hc)
  have hmove : ‖(x-y)-(P.center-Q.center)‖ ≤ 4/(2:ℝ)^p := by
    have hh := dist_sub_sub_le x y P.center Q.center
    rw [dist_eq_norm] at hh
    have h₁ := P.dist_le hP.le hx (P.center_mem hP)
    have h₂ := Q.dist_le hQ.le hy (Q.center_mem hQ)
    have hsum : dist x P.center+dist y Q.center ≤ 4/(2:ℝ)^p := by
      calc
        _ ≤ 2*P.side+2*Q.side := add_le_add h₁ h₂
        _ ≤ 2*(1/(2:ℝ)^p)+2*(1/(2:ℝ)^p) := by gcongr
        _ = _ := by ring
    exact hh.trans hsum
  have hbound : ‖(x-y)-(P.center-Q.center)‖^2/(2*‖P.center-Q.center‖) ≤ 1/(2:ℝ)^t := by
    rw [← dist_eq_norm]
    calc
      _ ≤ (4/(2:ℝ)^p)^2/(2*(96/(2:ℝ)^a)) :=
        div_le_div₀ (sq_nonneg _) (pow_le_pow_left₀ (norm_nonneg _) hmove 2)
          (by positivity) (mul_le_mul_of_nonneg_left hs (by norm_num))
      _ = ((2:ℝ)^a/((2:ℝ)^p)^2)/12 := by field_simp; ring
      _ ≤ (2:ℝ)^a/((2:ℝ)^p)^2 := by
        have hh : 0 ≤ (2:ℝ)^a/((2:ℝ)^p)^2 := by positivity
        linarith
      _ ≤ 1/(2:ℝ)^t := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        rw [one_mul,← pow_add,← pow_mul]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
  apply le_trans _ hbound
  simpa only [sourceRadialUnit,sourceRadialVector,ite_eq_right hc,dist_eq_norm] using hraw

namespace PositiveDistanceData

theorem suffix_distance_affine (d : PositiveDistanceData) (hQ : d.Q.side = 1)
    (hs : d.StronglySeparated) {p : ℕ} (hst : d.a+d.t ≤ 2*p)
    {P C : CellPath} (hP : P.length = p) (hC : C.length = p)
    (hPX : P.take d.a = d.X) (hCY : C.take d.a = d.Y)
    {x y : Plane} (hx : x ∈ (d.Q.descendant P).carrier)
    (hy : y ∈ (d.Q.descendant C).carrier) :
    |dist x y-planeDot (x-y)
      (sourceRadialUnit (d.Q.descendant C).center (d.Q.descendant P).center : Plane)| ≤
        1/(2:ℝ)^d.t := by
  have hside : 0 < d.Q.side := by rw [hQ]; norm_num
  exact fine_distance_affine_error _ _ (d.Q.descendant_side_pos hside P)
    (d.Q.descendant_side_pos hside C)
    (by simp only [DyadicSquare.descendant_side,hQ,hP,le_refl])
    (by simp only [DyadicSquare.descendant_side,hQ,hC,le_refl])
    (d.fine_endpoints_separated hside hs hPX hCY
      ((d.Q.descendant P).center_mem (d.Q.descendant_side_pos hside P))
      ((d.Q.descendant C).center_mem (d.Q.descendant_side_pos hside C))) hst hx hy

end PositiveDistanceData

end PlanarFalconer

end OAI
