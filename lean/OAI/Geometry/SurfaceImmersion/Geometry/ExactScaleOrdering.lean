import OAI.Geometry.SurfaceImmersion.Correction.CorrectionScaleAlgebra

namespace OAI

/-! Positivity and ordering of the actual scales in each correction step. -/
noncomputable section

namespace ClosedSurfaceR4.ExactCorrection

theorem exact_scale_positive {t : ℝ} (ht : 0 < t) (k : ℕ) :
    0 < t^((6/5 : ℝ)*((k : ℝ)+1)) ∧ 0 < t^(k : ℝ) ∧
      0 < t^(6/5 : ℝ) ∧ 0 < t^(11/10 : ℝ) :=
  ⟨Real.rpow_pos_of_pos ht _,Real.rpow_pos_of_pos ht _,
    Real.rpow_pos_of_pos ht _,Real.rpow_pos_of_pos ht _⟩

theorem exact_scale_order {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) {k : ℕ} (hk : 10 ≤ k) :
    t^((6/5 : ℝ)*((k : ℝ)+1)) ≤ t^(k : ℝ) ∧
      t^(k : ℝ) ≤ t^(6/5 : ℝ) ∧ t^(6/5 : ℝ) ≤ t^(11/10 : ℝ) ∧
      t^(11/10 : ℝ) ≤ t := by
  have hk' : (10 : ℝ) ≤ k := by exact_mod_cast hk
  refine ⟨Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith),
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith),
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num),?_⟩
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (show (1 : ℝ) ≤ 11/10 by norm_num)

theorem next_amplitude_scale {t : ℝ} (ht : 0 < t) (k : ℕ) :
    t^((6/5 : ℝ)*((k : ℝ)+1)) = (t^(6/5 : ℝ))^(k+1) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul ht.le]
  simp only [Nat.cast_add,Nat.cast_one]

theorem amplitude_scale_nat (t : ℝ) (k : ℕ) : t^(k : ℝ) = t^k :=
  Real.rpow_natCast t k

end ClosedSurfaceR4.ExactCorrection

end

end OAI
