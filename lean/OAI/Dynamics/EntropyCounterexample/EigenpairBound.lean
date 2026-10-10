import Mathlib

namespace OAI

noncomputable section

namespace Problem340

theorem eigenpair_modulus_le_of_norm_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →ₗ[ℝ] V) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ x, ‖A x‖ ≤ C * ‖x‖)
    (a b : ℝ) (u v : V) (hne : u ≠ 0 ∨ v ≠ 0)
    (hu : A u = a • u - b • v)
    (hv : A v = b • u + a • v) :
    Real.sqrt (a ^ 2 + b ^ 2) ≤ 2 * C := by
  have hab : 0 ≤ a ^ 2 + b ^ 2 := add_nonneg (sq_nonneg a) (sq_nonneg b)
  have hu' : (a ^ 2 + b ^ 2) • u = a • A u + b • A v := by
    rw [hu, hv]
    module
  have hv' : (a ^ 2 + b ^ 2) • v = (-b) • A u + a • A v := by
    rw [hu, hv]
    module
  have hnu : (a ^ 2 + b ^ 2) * ‖u‖ ≤ |a| * ‖A u‖ + |b| * ‖A v‖ := by
    calc
      (a ^ 2 + b ^ 2) * ‖u‖ = ‖(a ^ 2 + b ^ 2) • u‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hab]
      _ = ‖a • A u + b • A v‖ := congrArg norm hu'
      _ ≤ ‖a • A u‖ + ‖b • A v‖ := norm_add_le _ _
      _ = |a| * ‖A u‖ + |b| * ‖A v‖ := by simp [norm_smul]
  have hnv : (a ^ 2 + b ^ 2) * ‖v‖ ≤ |b| * ‖A u‖ + |a| * ‖A v‖ := by
    calc
      (a ^ 2 + b ^ 2) * ‖v‖ = ‖(a ^ 2 + b ^ 2) • v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hab]
      _ = ‖(-b) • A u + a • A v‖ := congrArg norm hv'
      _ ≤ ‖(-b) • A u‖ + ‖a • A v‖ := norm_add_le _ _
      _ = |b| * ‖A u‖ + |a| * ‖A v‖ := by simp [norm_smul]
  have hS : 0 < ‖u‖ + ‖v‖ := by
    rcases hne with hu0 | hv0
    · exact add_pos_of_pos_of_nonneg (norm_pos_iff.mpr hu0) (norm_nonneg v)
    · exact add_pos_of_nonneg_of_pos (norm_nonneg u) (norm_pos_iff.mpr hv0)
  have hsum : (a ^ 2 + b ^ 2) * (‖u‖ + ‖v‖) ≤
      ((|a| + |b|) * C) * (‖u‖ + ‖v‖) := by
    have h1 := mul_le_mul_of_nonneg_left (hA u) (abs_nonneg a)
    have h2 := mul_le_mul_of_nonneg_left (hA v) (abs_nonneg b)
    have h3 := mul_le_mul_of_nonneg_left (hA u) (abs_nonneg b)
    have h4 := mul_le_mul_of_nonneg_left (hA v) (abs_nonneg a)
    nlinarith
  have hbound : a ^ 2 + b ^ 2 ≤ (|a| + |b|) * C :=
    le_of_mul_le_mul_right hsum hS
  have ha : |a| ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
    exact Real.abs_le_sqrt (by nlinarith [sq_nonneg b])
  have hb : |b| ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
    exact Real.abs_le_sqrt (by nlinarith [sq_nonneg a])
  have hsqrt := Real.sq_sqrt hab
  have hroot := Real.sqrt_nonneg (a ^ 2 + b ^ 2)
  nlinarith [mul_le_mul_of_nonneg_right (add_le_add ha hb) hC]

theorem bddAbove_eigenpair_moduli_of_norm_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →ₗ[ℝ] V) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ x, ‖A x‖ ≤ C * ‖x‖) :
    BddAbove {r : ℝ | ∃ a b : ℝ, ∃ u v : V,
      (u ≠ 0 ∨ v ≠ 0) ∧ A u = a • u - b • v ∧
        A v = b • u + a • v ∧ r = Real.sqrt (a ^ 2 + b ^ 2)} := by
  refine ⟨2 * C, ?_⟩
  rintro r ⟨a, b, u, v, hne, hu, hv, rfl⟩
  exact eigenpair_modulus_le_of_norm_bound A C hC hA a b u v hne hu hv

theorem bddAbove_eigenpair_moduli_continuousLinearMap
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] V) :
    BddAbove {r : ℝ | ∃ a b : ℝ, ∃ u v : V,
      (u ≠ 0 ∨ v ≠ 0) ∧ A u = a • u - b • v ∧
        A v = b • u + a • v ∧ r = Real.sqrt (a ^ 2 + b ^ 2)} := by
  exact bddAbove_eigenpair_moduli_of_norm_bound A.toLinearMap ‖A‖
    (norm_nonneg A) A.le_opNorm

end Problem340

end

end OAI
