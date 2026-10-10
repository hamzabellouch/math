import OAI.Geometry.RCD.Heat.HeatBaseBounds
import OAI.Geometry.RCD.Heat.RescaledHeatEnvelope

namespace OAI

/-! # Cumulative constants uniform over a family of heat poles -/

open scoped BigOperators InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A uniform bound on the finite background and initial metric gives
one set of cumulative constants for every heat pole in a neighborhood.
The geometric absorption threshold is unchanged by the background. -/
theorem exists_uniform_heat_cumulative_constants
    {b T ε C : ℝ} (hb : 1 ≤ b) (hT : 0 < T) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (habsorb : 2 * C * (2 * geometricIntervalConstant ((3 / 4 : ℝ) * (9 / 8))) * ε ≤ 1 / 2) :
    ∃ A B D : ℝ, 0 < A ∧ 0 < B ∧ 0 < D ∧
    ∀ (Q : ℕ → E ≃L[ℝ] E) (N F : ℕ → E →L[ℝ] E) (J : ℕ),
    (∀ i, (Q i : E →L[ℝ] E).IsPositive) →
    (∀ i, (N i).IsPositive) →
    (∀ i, J ≤ i → ∀ v, ⟪v, Q i v⟫_ℝ ≤ (9 / 8 : ℝ) * ⟪v, Q (i + 1) v⟫_ℝ) →
    (∀ i, J ≤ i → ∀ v,
      let d := ⟪v, ((Q i : E →L[ℝ] E) - (Q (i + 1) : E →L[ℝ] E)) v⟫_ℝ
      0 ≤ d ∧ ⟪v, N i v⟫_ℝ ≤ C * d ∧ d ≤ C * ⟪v, F i v⟫_ℝ) →
    (∀ i, J ≤ i → ∀ v, ⟪v, N i v⟫_ℝ ≤ ε * ⟪v, Q i v⟫_ℝ) →
    (∀ i v, ⟪v, F (J + i) v⟫_ℝ ≤ b * (3 / 4 : ℝ) ^ i * ‖v‖ ^ 2 +
      ∑ j ∈ Finset.range (i + 1), (3 / 4 : ℝ) ^ (i - j) * ⟪v, N (J + j) v⟫_ℝ) →
    (∀ v, ⟪v, (Q J).symm v⟫_ℝ ≤ T * ‖v‖ ^ 2 ∧
      ‖v‖ ^ 2 ≤ T * ⟪v, (Q J).symm v⟫_ℝ) →
    (∀ v, ‖v‖ ^ 2 ≤ T * ⟪v, Q J v⟫_ℝ) →
    ∀ (xi : E) (k : ℕ),
      let H := ⟪xi, (Q (J + k)).symm xi⟫_ℝ
      let mass := ∑ i ∈ Finset.range k,
        ⟪(Q (J + i)).symm xi, N (J + i) ((Q (J + i)).symm xi)⟫_ℝ
      (∑ i ∈ Finset.range k,
        ⟪(Q (J + i)).symm xi, F (J + i) ((Q (J + i)).symm xi)⟫_ℝ) ≤ A * H ∧
      ‖xi‖ ^ 2 + mass ≤ B * H ∧ H ≤ D * (‖xi‖ ^ 2 + mass) := by
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  let R := T ^ 2 * (1 - (3 / 4 : ℝ) * (81 / 64))⁻¹
  let P := 2 * (1 - (3 / 4 : ℝ))⁻¹
  let W := 2 * geometricIntervalConstant ((3 / 4 : ℝ) * (9 / 8))
  have hR : 0 < R := by dsimp only [R]; positivity
  have hP : 0 < P := by norm_num [P]
  have hW : 0 ≤ W := mul_nonneg (by norm_num)
    (geometricIntervalConstant_nonneg (by norm_num))
  let A := b * (R * T + P * (b * C) + W * (b⁻¹ * ε)) + 1
  let B := b * (T + b * C) + 1
  let D := 2 * (T + 2 * b * C * R) + 4 * C * P + 1
  have hA : 0 < A := by dsimp only [A]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨A, B, D, hA, hB, hD, ?_⟩
  intro Q N F J hQ hN hstep hdecrement hsmall henv hQT hcoercivebase
  let Q' := fun i => Q (J + i)
  let N' := fun i => b⁻¹ • N (J + i)
  let F' := fun i => b⁻¹ • F (J + i)
  have hpos i : (Q' i : E →L[ℝ] E).IsPositive := hQ _
  have hNpos i : (N' i).IsPositive := (hN _).smul_of_nonneg (inv_pos.mpr hbpos).le
  have hstep' i v : ⟪v, Q' i v⟫_ℝ ≤ (9 / 8 : ℝ) * ⟪v, Q' (i + 1) v⟫_ℝ := by
    simpa only [Q', Nat.add_assoc] using hstep (J + i) (by omega) v
  have hdec i : ((Q' i : E →L[ℝ] E) - (Q' (i + 1) : E →L[ℝ] E)).IsPositive := by
    apply (ContinuousLinearMap.isPositive_iff _).mpr
    refine ⟨(hpos i).isSymmetric.sub (hpos (i + 1)).isSymmetric, ?_⟩
    intro v
    rw [real_inner_comm]
    simpa only [Q', Nat.add_assoc] using (hdecrement (J + i) (by omega) v).1
  have hscaled i v : ⟪v, N' i v⟫_ℝ ≤ (b * C) *
      ⟪v, ((Q' i : E →L[ℝ] E) - (Q' (i + 1) : E →L[ℝ] E)) v⟫_ℝ ∧
      ⟪v, ((Q' i : E →L[ℝ] E) - (Q' (i + 1) : E →L[ℝ] E)) v⟫_ℝ ≤
        (b * C) * ⟪v, F' i v⟫_ℝ := by
    apply rescaled_heat_decrements (N (J + i)) (F (J + i)) _ hb hC
    · intro w
      simpa only [Q', Nat.add_assoc] using (hdecrement (J + i) (by omega) w).1
    · intro w
      simpa only [Q', Nat.add_assoc] using (hdecrement (J + i) (by omega) w).2.1
    · intro w
      simpa only [Q', Nat.add_assoc] using (hdecrement (J + i) (by omega) w).2.2
  have hsmall' i v : ⟪v, N' i v⟫_ℝ ≤ (b⁻¹ * ε) * ⟪v, Q' i v⟫_ℝ := by
    have h := mul_le_mul_of_nonneg_left (hsmall (J + i) (by omega) v) (inv_pos.mpr hbpos).le
    simpa only [N', Q', smul_apply, inner_smul_right, mul_assoc] using h
  have henv' i v : ⟪v, F' i v⟫_ℝ ≤ (3 / 4 : ℝ) ^ i * ‖v‖ ^ 2 +
      ∑ j ∈ Finset.range (i + 1), (3 / 4 : ℝ) ^ (i - j) * ⟪v, N' j v⟫_ℝ :=
    rescaled_heat_envelope (fun j => N (J + j)) (fun j => F (J + j)) hbpos
      henv i v
  have hgrowth j i (hji : j ≤ i) v :
      ⟪v, Q' j v⟫_ℝ ≤ 1 * (9 / 8 : ℝ) ^ (i - j) * ⟪v, Q' i v⟫_ℝ := by
    simpa only [one_mul, ContinuousLinearEquiv.coe_coe] using geometric_form_growth
      (fun i => (Q' i : E →L[ℝ] E)) (by norm_num : (0 : ℝ) ≤ 9 / 8) hstep' hji v
  have hcoercive v : ‖v‖ ^ 2 ≤ T * ⟪v, Q' 0 v⟫_ℝ := by
    simpa only [Q', Nat.add_zero] using hcoercivebase v
  have hnorm := inverse_norm_sq_of_slow_growth_coercive Q' hT.le hstep' hcoercive
  intro xi k
  have h := inverse_heat_cumulative_comparison Q' N' F' hpos hNpos hdec
    (fun i => half_decrement_of_slow_step _ _ (hpos (i + 1)) (hstep' i))
    (mul_nonneg (inv_pos.mpr hbpos).le hε) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (sq_nonneg T) (by norm_num)
    (mul_nonneg hbpos.le hC) hT.le hgrowth hnorm hsmall' henv'
    (fun i v => (hscaled i v).1) (fun i v => (hscaled i v).2)
    (by simpa only [Q', Nat.add_zero] using hQT)
    (by rw [rescaled_absorption_identity hbpos]; simpa only [mul_one] using habsorb) xi k
  let mass := ∑ i ∈ Finset.range k,
    ⟪(Q (J + i)).symm xi, N (J + i) ((Q (J + i)).symm xi)⟫_ℝ
  let total := ∑ i ∈ Finset.range k,
    ⟪(Q (J + i)).symm xi, F (J + i) ((Q (J + i)).symm xi)⟫_ℝ
  let H := ⟪xi, (Q (J + k)).symm xi⟫_ℝ
  have hH : 0 ≤ H := (positive_equiv_symm _ (hQ _)).inner_nonneg_right xi
  have hm : 0 ≤ mass := Finset.sum_nonneg (fun i _ => (hN _).inner_nonneg_right _)
  simp only [N', F', Q', smul_apply, inner_smul_right, ← Finset.mul_sum, mul_one] at h
  change b⁻¹ * total ≤ (R * T + P * (b * C) + W * (b⁻¹ * ε)) * H ∧
    ‖xi‖ ^ 2 + b⁻¹ * mass ≤ (T + b * C) * H ∧
    H ≤ 2 * (T + 2 * (b * C) * R) * ‖xi‖ ^ 2 + 4 * (b * C) * P * (b⁻¹ * mass) at h
  change total ≤ A * H ∧ ‖xi‖ ^ 2 + mass ≤ B * H ∧ H ≤ D * (‖xi‖ ^ 2 + mass)
  have h₁ := mul_le_mul_of_nonneg_left h.1 hbpos.le
  have h₂ := mul_le_mul_of_nonneg_left h.2.1 hbpos.le
  have hcancel : b * b⁻¹ = 1 := mul_inv_cancel₀ hbpos.ne'
  have hterm : 4 * (b * C) * P * (b⁻¹ * mass) = 4 * C * P * mass := by field_simp
  rw [hterm] at h
  rw [mul_add] at h₂
  simp only [← mul_assoc, hcancel, one_mul] at h₁ h₂
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [A]
    nlinarith only [h₁, hH]
  · dsimp only [B]
    have hbxi := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖xi‖)
    nlinarith only [h₂, hH, hbxi]
  · dsimp only [D]
    have hc1 : 0 ≤ 2 * (T + 2 * b * C * R) := by positivity
    have hc2 : 0 ≤ 4 * C * P := by positivity
    nlinarith only [h.2.2, hm, sq_nonneg ‖xi‖, hc1, hc2]

end RegularPointCoordinates

end

end OAI
