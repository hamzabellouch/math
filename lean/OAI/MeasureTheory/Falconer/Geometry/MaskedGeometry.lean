import OAI.MeasureTheory.Falconer.Shells.MaskedDistanceBounds

namespace OAI

/-! # The fixed dimensional weight bounds in separated dyadic cells -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

 theorem DyadicCube.separated_pairs_upper (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : Q.side = P.side)
    (hsep : ‖P.center-Q.center‖ ≤ 2000*((d:ℝ)+1)*P.side)
    {x y : Space d} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) :
    dist x y ≤ 2002*((d:ℝ)+1)*P.side := by
  have hQp : 0 < Q.side := by rwa [hQ]
  have h₁ := P.dist_le hP.le hx (P.center_mem hP)
  have h₂ := Q.dist_le hQp.le (Q.center_mem hQp) hy
  rw [hQ] at h₂
  have hxy : dist x y ≤ dist x P.center+dist P.center Q.center+dist Q.center y :=
    (dist_triangle x P.center y).trans (by
      linarith [dist_triangle P.center Q.center y])
  have hs := mul_le_mul_of_nonneg_right (sqrt_dimension_le d) hP.le
  simp only [dist_eq_norm] at hxy h₁ h₂
  rw [dist_eq_norm]
  linarith

 theorem separated_cell_distance_bounds (Q : DyadicCube d) (hQ : Q.side = 1)
    (a : ℕ) (X Y : List (Fin d → Bool)) (hX : X.length = a) (hY : Y.length = a)
    (hlo : 125*((d:ℝ)+1)*(Q.descendant X).side ≤
      ‖(Q.descendant X).center-(Q.descendant Y).center‖)
    (hhi : ‖(Q.descendant X).center-(Q.descendant Y).center‖ ≤
      2000*((d:ℝ)+1)*(Q.descendant X).side)
    {x y : Space d} (hx : x ∈ (Q.descendant X).carrier) (hy : y ∈ (Q.descendant Y).carrier) :
    100*((d:ℝ)+1) ≤ dist x y*(2:ℝ)^a ∧
      dist x y*(2:ℝ)^a ≤ 2002*((d:ℝ)+1) := by
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have hside : (Q.descendant Y).side = (Q.descendant X).side := by
    rw [Q.descendant_side,Q.descendant_side,hX,hY]
  have hpx : (Q.descendant X).side = 1/(2:ℝ)^a := by rw [Q.descendant_side,hX,hQ]
  have hl := (Q.descendant X).separated_pairs_lower (Q.descendant Y)
    (Q.descendant_side_pos hQpos X) hside hlo hx hy
  have hu := (Q.descendant X).separated_pairs_upper (Q.descendant Y)
    (Q.descendant_side_pos hQpos X) hside hhi hx hy
  rw [hpx,← dist_eq_norm] at hl
  rw [hpx] at hu
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < (2:ℝ)^a)).mp
    simpa only [mul_one,div_eq_mul_inv,mul_assoc,one_mul] using hl
  · apply (le_div_iff₀ (by positivity : 0 < (2:ℝ)^a)).mp
    simpa only [mul_one,div_eq_mul_inv,mul_assoc,one_mul] using hu

end Falconer

end OAI
