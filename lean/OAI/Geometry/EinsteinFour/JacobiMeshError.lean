import OAI.Geometry.EinsteinFour.JacobiSchemeRatios
import OAI.Geometry.EinsteinFour.JacobiNormalized
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace OAI

/-! Error bounds at all nodes, including normalization through time zero. -/

namespace PositiveEinsteinFour.Jacobi

open scoped Matrix.Norms.L2Operator

noncomputable section

theorem relative_discrete_error {R : ℕ → NormalMatrix} {J : ℝ → NormalMatrix}
    {h t C K : ℝ} {N : ℕ} (hh : 0 < h) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hNt : ((N + 1 : ℕ) : ℝ) * h ≤ t)
    (hJ0 : J 0 = 0) (hJ : HasDerivAt J 1 0)
    (herr : ∀ i : ℕ, i ≤ N + 1 →
      ‖discretePosition R h i - J (i * h)‖ ≤ C * i * h ^ 2 * Real.exp (K * i * h)) :
    ∀ i : ℕ, i ≤ N + 1 →
      ‖relativeDiscretePosition R h i - normalizedJacobi J (i * h)‖ ≤
        C * h * Real.exp (K * t) := by
  intro i hi
  by_cases hi0 : i = 0
  · subst i
    simp only [relativeDiscretePosition_zero, Nat.cast_zero, zero_mul,
      normalizedJacobi_zero hJ, sub_self, norm_zero]
    positivity
  · have hip : 0 < i := Nat.pos_of_ne_zero hi0
    have hip' : (0 : ℝ) < i := by exact_mod_cast hip
    have hs : 0 < (i : ℝ) * h := mul_pos hip' hh
    have hit : (i : ℝ) * h ≤ t :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hh.le).trans hNt
    rw [relativeDiscretePosition_pos R h hip, normalizedJacobi_pos hJ0 hs.ne']
    have he := relative_position_error hip hh (herr i hi)
    simp only [one_div] at he
    exact he.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (by nlinarith : K * i * h ≤ K * t)) (mul_nonneg hC hh.le))

/-- The velocity used in a pivot is the next backward velocity. Its
distance from the velocity at the current node also tends to zero. -/
theorem next_discrete_velocity_error {R : ℕ → NormalMatrix} {V : ℝ → NormalMatrix}
    {h t C K L : ℝ} {N : ℕ} (hh : 0 < h) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (_hL : 0 ≤ L) (hNt : ((N + 1 : ℕ) : ℝ) * h ≤ t)
    (herr : ∀ i : ℕ, i ≤ N + 1 →
      ‖discreteVelocity R h i - V (i * h)‖ ≤ C * i * h ^ 2 * Real.exp (K * i * h))
    (hLip : ∀ s ∈ Set.Icc 0 t, ∀ r ∈ Set.Icc 0 t, ‖V s - V r‖ ≤ L * |s - r|) :
    ∀ i : ℕ, i ≤ N →
      ‖discreteVelocity R h (i + 1) - V (i * h)‖ ≤
        (C * t * Real.exp (K * t) + L) * h := by
  have ht : 0 ≤ t := (by positivity : 0 ≤ ((N + 1 : ℕ) : ℝ) * h).trans hNt
  have hmem (k : ℕ) (hk : k ≤ N + 1) : (k : ℝ) * h ∈ Set.Icc 0 t := by
    exact ⟨by positivity,
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hh.le).trans hNt⟩
  intro i hi
  have hin : i + 1 ≤ N + 1 := Nat.add_le_add_right hi 1
  have hb : ‖discreteVelocity R h (i + 1) - V ((i + 1 : ℕ) * h)‖ ≤
      C * t * h * Real.exp (K * t) := by
    calc
      _ ≤ C * (i + 1 : ℕ) * h ^ 2 * Real.exp (K * (i + 1 : ℕ) * h) := herr _ hin
      _ = (C * h) * (((i + 1 : ℕ) : ℝ) * h) *
          Real.exp (K * (((i + 1 : ℕ) : ℝ) * h)) := by ring_nf
      _ ≤ (C * h) * t * Real.exp (K * t) := by
        gcongr
        · exact (hmem _ hin).2
        · exact (hmem _ hin).2
      _ = _ := by ring_nf
  have hl := hLip _ (hmem _ hin) _ (hmem i (hi.trans (Nat.le_succ N)))
  have hdiff : |((i + 1 : ℕ) : ℝ) * h - (i : ℝ) * h| = h := by
    have heq : ((i + 1 : ℕ) : ℝ) * h - (i : ℝ) * h = h := by
      push_cast
      ring_nf
    rw [heq, abs_of_pos hh]
  rw [hdiff] at hl
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (discreteVelocity R h (i + 1)) (V ((i + 1 : ℕ) * h)) (V (i * h))
  nlinarith

end

end PositiveEinsteinFour.Jacobi

end OAI
