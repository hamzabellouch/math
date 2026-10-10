import OAI.Geometry.RCD.Heat.UniformCumulativeConstants

namespace OAI

/-! # Cumulative comparison after finitely many unrestricted initial scales -/

open scoped BigOperators InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The cumulative comparison only needs its smallness and decrement bounds
from some index onward. The earlier mass forms contribute a finite background;
the absorption threshold is independent of that background. -/
theorem eventual_heat_cumulative_comparison (Q : ℕ → E ≃L[ℝ] E)
    (N F : ℕ → E →L[ℝ] E) (J : ℕ)
    (hQ : ∀ i, (Q i : E →L[ℝ] E).IsPositive)
    (hN : ∀ i, (N i).IsPositive)
    {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hstep : ∀ i, J ≤ i → ∀ v,
      ⟪v, Q i v⟫_ℝ ≤ (9 / 8 : ℝ) * ⟪v, Q (i + 1) v⟫_ℝ)
    (hdecrement : ∀ i, J ≤ i → ∀ v,
      let d := ⟪v, ((Q i : E →L[ℝ] E) - (Q (i + 1) : E →L[ℝ] E)) v⟫_ℝ
      0 ≤ d ∧ ⟪v, N i v⟫_ℝ ≤ C * d ∧ d ≤ C * ⟪v, F i v⟫_ℝ)
    (hsmall : ∀ i, J ≤ i → ∀ v, ⟪v, N i v⟫_ℝ ≤ ε * ⟪v, Q i v⟫_ℝ)
    (henv : ∀ i v, ⟪v, F i v⟫_ℝ ≤ (3 / 4 : ℝ) ^ i * ‖v‖ ^ 2 +
      ∑ j ∈ Finset.range (i + 1), (3 / 4 : ℝ) ^ (i - j) * ⟪v, N j v⟫_ℝ)
    (habsorb : 2 * C * (2 * geometricIntervalConstant ((3 / 4 : ℝ) * (9 / 8))) * ε ≤ 1 / 2) :
    ∃ A B D : ℝ, 0 < A ∧ 0 < B ∧ 0 < D ∧ ∀ (xi : E) (k : ℕ),
      let H := ⟪xi, (Q (J + k)).symm xi⟫_ℝ
      let mass := ∑ i ∈ Finset.range k,
        ⟪(Q (J + i)).symm xi, N (J + i) ((Q (J + i)).symm xi)⟫_ℝ
      (∑ i ∈ Finset.range k,
        ⟪(Q (J + i)).symm xi, F (J + i) ((Q (J + i)).symm xi)⟫_ℝ) ≤ A * H ∧
      ‖xi‖ ^ 2 + mass ≤ B * H ∧ H ≤ D * (‖xi‖ ^ 2 + mass) := by
  let b := 1 + ∑ j ∈ Finset.range J, (3 / 4 : ℝ) ^ (J - j) * ‖N j‖
  have hb : 1 ≤ b := by
    dsimp only [b]
    have h := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range J) =>
      mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) (J - j)) (norm_nonneg (N j)))
    linarith
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  let T := 1 + ‖(Q J : E →L[ℝ] E)‖ + ‖((Q J).symm : E →L[ℝ] E)‖
  have hT : 0 < T := by dsimp only [T]; positivity
  have hQT : ∀ v, ⟪v, (Q J).symm v⟫_ℝ ≤ T * ‖v‖ ^ 2 ∧
      ‖v‖ ^ 2 ≤ T * ⟪v, (Q J).symm v⟫_ℝ := by
    intro v
    have h := positive_equiv_inverse_comparison (Q J) (hQ J) v
    have hp := (positive_equiv_symm (Q J) (hQ J)).inner_nonneg_right v
    constructor
    · exact h.1.trans (mul_le_mul_of_nonneg_right (by dsimp only [T]; linarith [norm_nonneg (Q J : E →L[ℝ] E)]) (sq_nonneg _))
    · exact h.2.trans (mul_le_mul_of_nonneg_right (by dsimp only [T]; linarith [norm_nonneg ((Q J).symm : E →L[ℝ] E)]) hp)
  obtain ⟨A, B, D, hA, hB, hD, hresult⟩ :=
    exists_uniform_heat_cumulative_constants (E := E) hb hT hε hC habsorb
  refine ⟨A, B, D, hA, hB, hD, hresult Q N F J hQ hN hstep hdecrement hsmall ?_ hQT ?_⟩
  · exact shifted_heat_envelope_bound N F (by norm_num) (by norm_num) henv J
  · intro v
    have hi := positive_equiv_inverse_comparison (Q J).symm (positive_equiv_symm (Q J) (hQ J)) v
    have hp := (hQ J).inner_nonneg_right v
    simpa only [ContinuousLinearEquiv.symm_symm] using
      hi.2.trans (mul_le_mul_of_nonneg_right (by dsimp only [T]; linarith [norm_nonneg (Q J : E →L[ℝ] E)]) hp)

end RegularPointCoordinates

end

end OAI
