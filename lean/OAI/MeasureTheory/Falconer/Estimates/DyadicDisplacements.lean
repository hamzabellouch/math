import OAI.MeasureTheory.Falconer.Estimates.DyadicTree

namespace OAI

/-!
# Point replacement errors in the original dyadic cubes

The two points of an internal displacement belong to different descendants
of the same parent. No separation between the two endpoint parents enters
these estimates.
-/

namespace Falconer

theorem DyadicCube.descendant_displacement_error {d n : ℕ}
    (Q : DyadicCube d) (hQ : 0 < Q.side) (p q : List (Fin d → Bool))
    (hp : p.length = n) (hq : q.length = n) {x x' : Space d}
    (hx : x ∈ (Q.descendant p).carrier) (hx' : x' ∈ (Q.descendant q).carrier) :
    ‖(x-x')-((Q.descendant p).center-(Q.descendant q).center)‖ ≤
      2*Real.sqrt d*(Q.side/(2 : ℝ)^n) := by
  have h₁ := (Q.descendant p).dist_le (Q.descendant_side_pos hQ p).le hx
    ((Q.descendant p).center_mem (Q.descendant_side_pos hQ p))
  have h₂ := (Q.descendant q).dist_le (Q.descendant_side_pos hQ q).le hx'
    ((Q.descendant q).center_mem (Q.descendant_side_pos hQ q))
  rw [Q.descendant_side,hp,dist_eq_norm] at h₁
  rw [Q.descendant_side,hq,dist_eq_norm] at h₂
  have he : (x-x')-((Q.descendant p).center-(Q.descendant q).center) =
      (x-(Q.descendant p).center)-(x'-(Q.descendant q).center) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

theorem DyadicCube.descendant_displacement_bound {d : ℕ}
    (Q : DyadicCube d) (hQ : 0 < Q.side) (p q : List (Fin d → Bool))
    {x x' : Space d} (hx : x ∈ (Q.descendant p).carrier)
    (hx' : x' ∈ (Q.descendant q).carrier) :
    ‖x-x'‖ ≤ Real.sqrt d*Q.side := by
  simpa only [dist_eq_norm] using Q.dist_le hQ.le
    (Q.descendant_subset p hx) (Q.descendant_subset q hx')

theorem DyadicCube.descendant_center_displacement_bound {d : ℕ}
    (Q : DyadicCube d) (hQ : 0 < Q.side) (p q : List (Fin d → Bool)) :
    ‖(Q.descendant p).center-(Q.descendant q).center‖ ≤ Real.sqrt d*Q.side :=
  Q.descendant_displacement_bound hQ p q
    ((Q.descendant p).center_mem (Q.descendant_side_pos hQ p))
    ((Q.descendant q).center_mem (Q.descendant_side_pos hQ q))

theorem DyadicCube.descendant_cap_error {d n : ℕ}
    (Q : DyadicCube d) (hQ : 0 < Q.side) (p q : List (Fin d → Bool))
    (hp : p.length = n) (hq : q.length = n) {x x' : Space d}
    (hx : x ∈ (Q.descendant p).carrier) (hx' : x' ∈ (Q.descendant q).carrier)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ‖(x-x')-((Q.descendant p).center-(Q.descendant q).center)‖ +
        8*δ*‖(Q.descendant p).center-(Q.descendant q).center‖ ≤
      2*Real.sqrt d*(Q.side/(2 : ℝ)^n)+8*δ*(Real.sqrt d*Q.side) :=
  add_le_add (Q.descendant_displacement_error hQ p q hp hq hx hx')
    (mul_le_mul_of_nonneg_left (Q.descendant_center_displacement_bound hQ p q) (by positivity))

end Falconer

end OAI
