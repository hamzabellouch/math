import OAI.Combinatorics.Crossing.TruncatedChainVertices

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b : Plane}

def truncatedScale (P : PolygonalChain O a b) (r : ℝ) (i : ℕ) : ℝ :=
  1-(if i=0 then P.startFraction r else 0)-(if i+1=P.pieces then P.endFraction r else 0)

theorem truncated_start_formula (P : PolygonalChain O a b) (r : ℝ) (i : ℕ) (hi : i < P.pieces) :
    P.truncatedVertices r i=P.vertices i+(if i=0 then P.startFraction r else 0) • trackDirection P.vertices i := by
  by_cases h : i=0
  · subst i
    rw [truncatedVertices_first,startPort_eq_fraction]
    rfl
  · simp only [truncatedVertices,ite_eq_right h,ite_eq_right (show i ≠ P.pieces by omega),zero_smul,add_zero]

theorem truncated_end_formula (P : PolygonalChain O a b) (r : ℝ) (i : ℕ) (_hi : i < P.pieces) :
    P.truncatedVertices r (i+1)=P.vertices (i+1)-(if i+1=P.pieces then P.endFraction r else 0) •
      trackDirection P.vertices i := by
  by_cases h : i+1=P.pieces
  · have hh : i=P.pieces-1 := by omega
    rw [h,truncatedVertices_last P (by omega) r,endPort_eq_fraction,ite_eq_left rfl]
    simp only [trackDirection,hh,show P.pieces-1+1=P.pieces by omega]
  · simp only [truncatedVertices,ite_eq_right (show i+1 ≠ 0 by omega),ite_eq_right h,zero_smul,sub_zero]

theorem truncated_direction (P : PolygonalChain O a b) (r : ℝ) (i : ℕ) (hi : i < P.pieces) :
    trackDirection (P.truncatedVertices r) i=P.truncatedScale r i • trackDirection P.vertices i := by
  change P.truncatedVertices r (i+1)-P.truncatedVertices r i=_
  rw [truncated_end_formula P r i hi,truncated_start_formula P r i hi]
  apply Prod.ext <;> dsimp [trackDirection,truncatedScale] <;> ring

theorem truncatedScale_pos (P : PolygonalChain O a b) (r : ℝ) (hr : 0 < r)
    (hfirst : 4*r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : 4*r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1))) (i : ℕ) :
    0 < P.truncatedScale r i := by
  have hs := radialPort_parameter_half (P.vertices 0) (P.vertices 1) r hr hfirst
  have he := radialPort_parameter_half (P.vertices (P.pieces-1)) (P.vertices P.pieces) r hr hlast
  change 0 < P.startFraction r ∧ P.startFraction r < 1/2 at hs
  change 0 < P.endFraction r ∧ P.endFraction r < 1/2 at he
  unfold truncatedScale
  split_ifs <;> linarith

theorem truncated_direction_ne_zero (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hfirst : 4*r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : 4*r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1)))
    (i : ℕ) (hi : i < P.pieces) : trackDirection (P.truncatedVertices r) i ≠ 0 := by
  rw [P.truncated_direction r i hi]
  exact smul_ne_zero (ne_of_gt (P.truncatedScale_pos r hr hfirst hlast i)) (P.minimum_piece_ne_zero hmin i hi)

end Zarankiewicz.PolygonalChain

end

end OAI
