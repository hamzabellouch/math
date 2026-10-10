import OAI.Geometry.HeilbronnTriangle.Definitions

namespace OAI


noncomputable section

namespace Problem355.Homogeneous

abbrev Column := Fin 3 → ℝ

def project (u : Column) : ℝ × ℝ := (u 0 / u 2, u 1 / u 2)

def columns (u v w : Column) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![u 0, v 0, w 0; u 1, v 1, w 1; u 2, v 2, w 2]

theorem project_cross_eq (u v w : Column)
    (hu : u 2 ≠ 0) (hv : v 2 ≠ 0) (hw : w 2 ≠ 0) :
    ((v 0 / v 2 - u 0 / u 2) * (w 1 / w 2 - u 1 / u 2) -
      (v 1 / v 2 - u 1 / u 2) * (w 0 / w 2 - u 0 / u 2)) =
      (columns u v w).det / (u 2 * v 2 * w 2) := by
  simp [columns, Matrix.det_fin_three]
  field_simp
  ring

theorem project_area_eq (u v w : Column)
    (hu : 0 < u 2) (hv : 0 < v 2) (hw : 0 < w 2) :
    triangleArea (project u) (project v) (project w) =
      |(columns u v w).det| / (2 * u 2 * v 2 * w 2) := by
  unfold triangleArea project
  dsimp only
  rw [project_cross_eq u v w (ne_of_gt hu) (ne_of_gt hv) (ne_of_gt hw),
    abs_div, abs_of_pos (mul_pos (mul_pos hu hv) hw), div_div]
  congr 1
  ring

def InBox (N : ℝ) (u : Column) : Prop :=
  0 ≤ u 0 ∧ u 0 < N ∧ 0 ≤ u 1 ∧ u 1 < N ∧ N ≤ u 2 ∧ u 2 < 2 * N

theorem project_in_unit_square {N : ℝ} (hN : 0 < N) {u : Column}
    (hu : InBox N u) : pointInUnitSquare (project u) := by
  rcases hu with ⟨hu0, hu0N, hu1, hu1N, hNu2, _⟩
  have hu2 : 0 < u 2 := lt_of_lt_of_le hN hNu2
  exact ⟨div_nonneg hu0 hu2.le, (div_le_one hu2).2 (le_trans hu0N.le hNu2),
    div_nonneg hu1 hu2.le, (div_le_one hu2).2 (le_trans hu1N.le hNu2)⟩

theorem project_area_lower_bound {N τ : ℝ} (hN : 0 < N) (hτ : 0 ≤ τ)
    (u v w : Column)
    (hu : N ≤ u 2) (hu' : u 2 ≤ 2 * N)
    (hv : N ≤ v 2) (hv' : v 2 ≤ 2 * N)
    (hw : N ≤ w 2) (hw' : w 2 ≤ 2 * N)
    (hdet : τ ≤ |(columns u v w).det|) :
    τ / (16 * N ^ 3) ≤ triangleArea (project u) (project v) (project w) := by
  have hu0 : 0 < u 2 := lt_of_lt_of_le hN hu
  have hv0 : 0 < v 2 := lt_of_lt_of_le hN hv
  have hw0 : 0 < w 2 := lt_of_lt_of_le hN hw
  have hden0 : 0 < 2 * u 2 * v 2 * w 2 := by positivity
  have hden : 2 * u 2 * v 2 * w 2 ≤ 16 * N ^ 3 := by
    calc
      2 * u 2 * v 2 * w 2 ≤ 2 * (2 * N) * (2 * N) * (2 * N) := by gcongr
      _ = 16 * N ^ 3 := by ring
  rw [project_area_eq u v w hu0 hv0 hw0]
  exact (div_le_div_of_nonneg_left hτ hden0 hden).trans
    (div_le_div_of_nonneg_right hdet hden0.le)

theorem project_area_lower_bound_of_box {N τ : ℝ} (hN : 0 < N) (hτ : 0 ≤ τ)
    {u v w : Column} (hu : InBox N u) (hv : InBox N v) (hw : InBox N w)
    (hdet : τ ≤ |(columns u v w).det|) :
    τ / (16 * N ^ 3) ≤ triangleArea (project u) (project v) (project w) :=
  project_area_lower_bound hN hτ u v w hu.2.2.2.2.1 hu.2.2.2.2.2.le
    hv.2.2.2.2.1 hv.2.2.2.2.2.le hw.2.2.2.2.1 hw.2.2.2.2.2.le hdet

end Problem355.Homogeneous

end

end OAI
