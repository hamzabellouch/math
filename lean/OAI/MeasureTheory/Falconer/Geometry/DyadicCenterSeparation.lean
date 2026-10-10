import OAI.MeasureTheory.Falconer.Geometry.ScaledDyadicPacking

namespace OAI

namespace PlanarFalconer
open Set Metric

theorem DyadicSquare.center_separation (P Q : DyadicSquare)
    (hs : P.side = Q.side) (hd : Disjoint P.carrier Q.carrier) :
    P.side ≤ dist P.center Q.center := by
  by_contra h
  have hh : dist P.center Q.center < P.side := lt_of_not_ge h
  have h0 := abs_lt.mp ((plane_coordinate_dist_le P.center Q.center 0).trans_lt hh)
  have h1 := abs_lt.mp ((plane_coordinate_dist_le P.center Q.center 1).trans_lt hh)
  simp only [DyadicSquare.center,WithLp.ofLp_toLp,Matrix.cons_val_zero,
    Matrix.cons_val_one] at h0 h1
  let z : Plane := WithLp.toLp 2 ![(P.x+Q.x+P.side)/2,(P.y+Q.y+P.side)/2]
  have hP : z ∈ P.carrier := by
    simp only [DyadicSquare.carrier,mem_ofPred_eq,z,Matrix.cons_val_zero,
      Matrix.cons_val_one]
    constructor
    · linarith
    · exact ⟨by linarith,by linarith,by linarith⟩
  have hQ : z ∈ Q.carrier := by
    simp only [DyadicSquare.carrier,mem_ofPred_eq,z,Matrix.cons_val_zero,
      Matrix.cons_val_one]
    constructor
    · linarith
    · exact ⟨by linarith,by linarith,by linarith⟩
  exact Set.disjoint_left.mp hd hP hQ

theorem dyadic_centers_separated (Q : DyadicSquare) (hQ : 0 < Q.side)
    {n : ℕ} {p q : List (Bool × Bool)} (hp : p.length = n) (hq : q.length = n) (hne : p ≠ q) :
    Q.side/(2:ℝ)^n ≤ dist (Q.descendant p).center (Q.descendant q).center := by
  have hs : (Q.descendant p).side = (Q.descendant q).side := by
    rw [Q.descendant_side,Q.descendant_side,hp,hq]
  have hh := (Q.descendant p).center_separation (Q.descendant q) hs
    (Q.descendants_disjoint hQ (hp.trans hq.symm) hne)
  simpa only [Q.descendant_side,hp] using hh

end PlanarFalconer

end OAI
