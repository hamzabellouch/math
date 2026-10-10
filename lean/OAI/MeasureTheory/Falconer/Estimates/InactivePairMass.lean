import OAI.MeasureTheory.Falconer.Measures.DyadicIntegralSplitting

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem normalized_pair_integral_norm_le (ρ ν : Measure Plane)
    [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (X Y : Set Plane)
    {M₁ M₂ ε : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (F : Plane → Plane → ℂ) (hb : ∀ x ∈ X, ∀ y ∈ Y, ‖F x y‖ ≤ ε) :
    ‖(M₁*M₂)⁻¹ • (∫ x in X, ∫ y in Y, F x y ∂ν ∂ρ)‖ ≤
      ε * ((ρ X).toReal/M₁) * ((ν Y).toReal/M₂) := by
  have hy (x : Plane) (hx : x ∈ X) : ‖∫ y in Y, F x y ∂ν‖ ≤ ε*(ν Y).toReal :=
    norm_setIntegral_le_of_norm_le_const (measure_lt_top ν Y) (hb x hx)
  have hx := norm_setIntegral_le_of_norm_le_const (measure_lt_top ρ X) hy
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (mul_pos hM₁ hM₂))]
  apply (mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ (M₁*M₂)⁻¹)).trans_eq
  simp only [div_eq_mul_inv, mul_inv_rev, Measure.real]
  ac_rfl

theorem occupied_pair_error_sum_le (P Q : DyadicSquare) (hP : 0 < P.side) (hQ : 0 < Q.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (n m : ℕ)
    {M₁ M₂ ε : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (F : CellPath → CellPath → Plane → Plane → ℂ)
    (hb : ∀ A ∈ occupiedAnchorPaths P ρ n, ∀ B ∈ occupiedAnchorPaths Q ν m,
      ∀ x ∈ (P.descendant A).carrier, ∀ y ∈ (Q.descendant B).carrier, ‖F A B x y‖ ≤ ε) :
    ‖∑ A ∈ occupiedAnchorPaths P ρ n, ∑ B ∈ occupiedAnchorPaths Q ν m,
      (M₁*M₂)⁻¹ • (∫ x in (P.descendant A).carrier, ∫ y in (Q.descendant B).carrier,
        F A B x y ∂ν ∂ρ)‖ ≤ ε*((ρ P.carrier).toReal/M₁)*((ν Q.carrier).toReal/M₂) := by
  calc
    _ ≤ ∑ A ∈ occupiedAnchorPaths P ρ n, ∑ B ∈ occupiedAnchorPaths Q ν m,
        ε*((ρ (P.descendant A).carrier).toReal/M₁)*((ν (Q.descendant B).carrier).toReal/M₂) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro A hA
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro B hB
      exact normalized_pair_integral_norm_le ρ ν _ _ hM₁ hM₂ _ (hb A hA B hB)
    _ = _ := by
      simp only [← Finset.mul_sum]
      rw [Q.normalized_mass_split hQ ν m M₂, ← Finset.sum_mul, ← Finset.mul_sum,
        P.normalized_mass_split hP ρ n M₁]

theorem complex_squared_norm_error (z e : ℂ) :
    |‖z+e‖^2-‖z‖^2| ≤ 2*‖z‖*‖e‖+‖e‖^2 := by
  have htri := norm_add_le z e
  have hrev := norm_add_le (z+e) (-e)
  simp only [add_neg_cancel_right, norm_neg] at hrev
  have hd := abs_norm_sub_norm_le (z+e) z
  simp only [add_sub_cancel_left] at hd
  have hid : ‖z+e‖^2-‖z‖^2 = (‖z+e‖-‖z‖)*(‖z+e‖+‖z‖) := by ring
  rw [hid, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc
    _ ≤ ‖e‖*(2*‖z‖+‖e‖) := mul_le_mul hd (by linarith) (by positivity) (norm_nonneg _)
    _ = _ := by ring

end PlanarFalconer

end OAI
