import OAI.Geometry.TranslativeCovering.CapOverlap

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace ProjectiveCaps
open InnerProductGeometry Real
variable {V : Type u_1} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable def angle (x y : V) : ℝ :=
  min (InnerProductGeometry.angle x y) (InnerProductGeometry.angle x (-y))

lemma angle_nonneg (x y : V) : 0 ≤ angle x y :=
  le_min (InnerProductGeometry.angle_nonneg _ _) (InnerProductGeometry.angle_nonneg _ _)

lemma angle_self {x : V} (hx : x ≠ 0) : angle x x = 0 := by
  rw [angle, InnerProductGeometry.angle_self hx, min_eq_left]
  exact InnerProductGeometry.angle_nonneg _ _

lemma angle_comm (x y : V) : angle x y = angle y x := by
  simp only [angle, InnerProductGeometry.angle_neg_right]
  rw [InnerProductGeometry.angle_comm x y]

lemma angle_triangle (x y z : V) : angle x z ≤ angle x y + angle y z := by
  unfold angle
  by_cases hxy : InnerProductGeometry.angle x y ≤ InnerProductGeometry.angle x (-y)
  · rw [min_eq_left hxy]
    by_cases hyz : InnerProductGeometry.angle y z ≤ InnerProductGeometry.angle y (-z)
    · rw [min_eq_left hyz]
      exact (min_le_left _ _).trans (InnerProductGeometry.angle_le_angle_add_angle x y z)
    · rw [min_eq_right (le_of_not_ge hyz)]
      exact (min_le_right _ _).trans (InnerProductGeometry.angle_le_angle_add_angle x y (-z))
  · rw [min_eq_right (le_of_not_ge hxy)]
    by_cases hyz : InnerProductGeometry.angle y z ≤ InnerProductGeometry.angle y (-z)
    · rw [min_eq_left hyz]
      have h := InnerProductGeometry.angle_le_angle_add_angle x (-y) (-z)
      rw [InnerProductGeometry.angle_neg_neg] at h
      exact (min_le_right _ _).trans h
    · rw [min_eq_right (le_of_not_ge hyz)]
      have h := InnerProductGeometry.angle_le_angle_add_angle x (-y) z
      have he : InnerProductGeometry.angle (-y) z = InnerProductGeometry.angle y (-z) := by
        simp only [InnerProductGeometry.angle_neg_left, InnerProductGeometry.angle_neg_right]
      rw [he] at h
      exact (min_le_left _ _).trans h

noncomputable def costDist {I : Type u_2} (n : ℕ) (x : I → V) (s : I → ℝ) (i j : I) : ℝ :=
  Real.sqrt n * angle (x i) (x j) + Real.sqrt |s i-s j|

lemma costDist_nonneg {I : Type u_3} (n : ℕ) (x : I → V) (s : I → ℝ) (i j : I) :
    0 ≤ costDist n x s i j :=
  add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (angle_nonneg _ _)) (Real.sqrt_nonneg _)

lemma costDist_self {I : Type u_4} (n : ℕ) (x : I → V) (s : I → ℝ)
    (hx : ∀ i, x i ≠ 0) (i : I) : costDist n x s i i = 0 := by
  simp [costDist, angle_self (hx i)]

lemma costDist_comm {I : Type u_5} (n : ℕ) (x : I → V) (s : I → ℝ) (i j : I) :
    costDist n x s i j = costDist n x s j i := by
  rw [costDist, costDist, angle_comm, abs_sub_comm]

lemma costDist_triangle {I : Type u_6} (n : ℕ) (x : I → V) (s : I → ℝ) (i j k : I) :
    costDist n x s i k ≤ costDist n x s i j + costDist n x s j k := by
  have ha := mul_le_mul_of_nonneg_left (angle_triangle (x i) (x j) (x k)) (Real.sqrt_nonneg (n:ℝ))
  have hb : Real.sqrt |s i-s k| ≤ Real.sqrt |s i-s j| + Real.sqrt |s j-s k| :=
    (Real.sqrt_le_sqrt (abs_sub_le (s i) (s j) (s k))).trans (by
      have h1 := Real.sq_sqrt (abs_nonneg (s i-s j))
      have h2 := Real.sq_sqrt (abs_nonneg (s j-s k))
      have h3 := Real.sq_sqrt (add_nonneg (abs_nonneg (s i-s j)) (abs_nonneg (s j-s k)))
      nlinarith [Real.sqrt_nonneg |s i-s j|, Real.sqrt_nonneg |s j-s k|,
        Real.sqrt_nonneg (|s i-s j|+|s j-s k|),
        mul_nonneg (Real.sqrt_nonneg |s i-s j|) (Real.sqrt_nonneg |s j-s k|)])
  dsimp [costDist]
  nlinarith

end ProjectiveCaps

end OAI
