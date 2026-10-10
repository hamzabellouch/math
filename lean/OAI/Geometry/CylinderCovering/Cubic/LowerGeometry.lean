import OAI.Geometry.TriangularCovering.Main

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
open TriangularCovering

namespace CubicLowerGeometry

def vertices (a b T : ℝ) : Fin 3 → Space :=
  ![point 0 0 (-1), point 0 (a * T) (T - 1), point 0 (b * T) (T - 1)]

lemma triple (a b T ε A B : ℝ) :
    inner ℝ (unit (tiltV ε A B))
      (cross3 (vertices a b T 1 - vertices a b T 0)
        (vertices a b T 2 - vertices a b T 0)) =
      H * (a - b) * T ^ 2 / ‖tiltV ε A B‖ := by
  simp only [TriangularCovering.unit, inner_smul_left, conj_trivial, inner_coord, cross3_coord]
  dsimp [vertices, point, tiltV]
  ring

lemma triple_ne_zero {a b T : ℝ} (hab : a < b) (hT : 0 < T)
    (ε A B : ℝ) :
    inner ℝ (unit (tiltV ε A B))
      (cross3 (vertices a b T 1 - vertices a b T 0)
        (vertices a b T 2 - vertices a b T 0)) ≠ 0 := by
  rw [triple]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero H_ne_zero
    (sub_ne_zero.mpr (ne_of_lt hab))) (pow_ne_zero _ (ne_of_gt hT)))
    (norm_ne_zero_iff.mpr (tiltV_ne_zero ε A B))

def lowerCylinder {a b T : ℝ} (hab : a < b) (hT : 0 < T)
    (ε A B : ℝ) : TriCylinder :=
  projectedCylinder (unit (tiltV ε A B)) (unit_norm (tiltV_ne_zero ε A B))
    (vertices a b T 0) (vertices a b T 1) (vertices a b T 2)
    (triple_ne_zero hab hT ε A B)

lemma lowerCylinder_axis {a b T : ℝ} (hab : a < b) (hT : 0 < T)
    (ε A B : ℝ) :
    (lowerCylinder hab hT ε A B).axis = unit (tiltV ε A B) := rfl

lemma lowerCylinder_area {a b T : ℝ} (hab : a < b) (hT : 0 < T)
    (ε A B : ℝ) :
    area (lowerCylinder hab hT ε A B).base =
      H * (b - a) * T ^ 2 / (2 * Real.sqrt (1 + ε ^ 2 * (A ^ 2 + 2 * B ^ 2))) := by
  rw [lowerCylinder, projectedCylinder_area, triple, tiltV_norm]
  rw [abs_div, abs_mul, abs_mul, abs_of_pos H_pos,
    abs_of_neg (sub_neg.mpr hab), abs_sq, abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

lemma triangle_mem {a b T y s : ℝ} (hab : a < b) (hT : 0 < T)
    (hs0 : 0 ≤ s) (hsT : s ≤ T) (hay : a * s ≤ y) (hyb : y ≤ b * s) :
    point 0 y (s - 1) ∈ triangle (vertices a b T 0)
      (vertices a b T 1) (vertices a b T 2) := by
  obtain ⟨r, q, hr, hq, hrq, hes, hey⟩ := sector_weights hab hT hs0 hsT hay hyb
  rw [mem_triangle_iff]
  refine ⟨r, q, hr, hq, hrq, ?_⟩
  ext i
  fin_cases i <;> dsimp [vertices, point]
  · ring
  · nlinarith only [hey]
  · linear_combination -H * hes

lemma triangle_mem_iff {a b T y s : ℝ} (hab : a < b) (hT : 0 < T) :
    point 0 y (s - 1) ∈ triangle (vertices a b T 0)
      (vertices a b T 1) (vertices a b T 2) ↔
      0 ≤ s ∧ s ≤ T ∧ a * s ≤ y ∧ y ≤ b * s := by
  constructor
  · intro hm
    obtain ⟨r, q, hr, hq, hrq, hv⟩ := (mem_triangle_iff _ _ _ _).mp hm
    have hy := congrArg (fun v : Space => v 1) hv
    have hs := congrArg (fun v : Space => v 2) hv
    dsimp [vertices, point] at hy hs
    have hsr : s = r * T + q * T := by
      apply mul_left_cancel₀ H_ne_zero
      nlinarith only [hs]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hsr]
      positivity
    · nlinarith [mul_le_mul_of_nonneg_right hrq hT.le]
    · rw [hsr, hy]
      nlinarith [mul_nonneg hq (mul_nonneg (sub_nonneg.mpr hab.le) hT.le)]
    · rw [hsr, hy]
      nlinarith [mul_nonneg hr (mul_nonneg (sub_nonneg.mpr hab.le) hT.le)]
  · rintro ⟨hs, hsT, hl, hu⟩
    exact triangle_mem hab hT hs hsT hl hu

lemma lowerCylinder_hit {a b T : ℝ} (hab : a < b) (hT : 0 < T)
    (ε A B x y z : ℝ)
    (hs0 : 0 ≤ 1 + z - ε * x * B) (hsT : 1 + z - ε * x * B ≤ T)
    (hl : a * (1 + z - ε * x * B) ≤ y - ε * x * A)
    (hu : y - ε * x * A ≤ b * (1 + z - ε * x * B)) :
    point x y z ∈ (lowerCylinder hab hT ε A B).carrier := by
  apply projectedCylinder_mem_direction (tiltV ε A B) (tiltV_ne_zero ε A B)
    _ _ _ _ (triangle_mem hab hT hs0 hsT hl hu) x
  ext i
  fin_cases i <;> dsimp [point, tiltV] <;> ring

end CubicLowerGeometry

end

end OAI
