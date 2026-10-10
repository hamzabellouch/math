import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDefectExclusion

namespace OAI

/-! # The exact derivative-row comparison implies the radial L² obstruction

This is the quantitative two-channel inequality used after the falling-Euler
row and the differentiated outgoing remainder have been identified.
-/

open Set Filter Topology MeasureTheory

namespace DefocusingNLS

local notation "V" => ℂ × ℂ
local notation "End" => V →L[ℂ] V

theorem homogeneousPair_energy_control (w x : V) (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c)
    (h : c * a * ‖w‖ ≤ ‖x‖ + b) :
    a ^ 2 * homogeneousPairEnergy w ≤
      (4 / c ^ 2) * homogeneousPairEnergy x + (4 / c ^ 2) * b ^ 2 := by
  have hs : (c * a * ‖w‖) ^ 2 ≤ (‖x‖ + b) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 h
  have hew := mul_le_mul_of_nonneg_left (homogeneousPairEnergy_upper w)
    (sq_nonneg (c * a))
  have hex := homogeneousPairEnergy_lower x
  have hsum : (‖x‖ + b) ^ 2 ≤ 2 * homogeneousPairEnergy x + 2 * b ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ - b)]
  have htotal : c ^ 2 * (a ^ 2 * homogeneousPairEnergy w) ≤
      4 * homogeneousPairEnergy x + 4 * b ^ 2 := by
    calc
      _ ≤ 2 * (c * a * ‖w‖) ^ 2 := by convert hew using 1 <;> ring
      _ ≤ 2 * (‖x‖ + b) ^ 2 := mul_le_mul_of_nonneg_left hs (by norm_num)
      _ ≤ _ := by linarith
  have hdiv := (le_div_iff₀ (sq_pos_of_pos hc)).2
    (show a ^ 2 * homogeneousPairEnergy w * c ^ 2 ≤
      4 * homogeneousPairEnergy x + 4 * b ^ 2 by simpa only [mul_comm] using htotal)
  convert hdiv using 1
  ring

theorem homogeneousRadial_derivative_comparison
    (U W H : V) (T R : End) (r beta c K M : ℝ) (N : ℕ)
    (hr : 0 < r) (hc : 0 < c) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hrow : c * r ^ beta * ‖W‖ ≤ ‖T W‖)
    (hidentity : H = T W + R U)
    (hR : ‖R‖ ≤ K * r ^ (-(N : ℝ))) (hU : ‖U‖ ≤ M) :
    r ^ (2 * beta) * homogeneousPairEnergy W ≤
      (4 / c ^ 2) * homogeneousPairEnergy H +
        (4 / c ^ 2) * (K * M) ^ 2 * r ^ (-2 * (N : ℝ)) := by
  have hRnorm : ‖R U‖ ≤ K * r ^ (-(N : ℝ)) * M :=
    (ContinuousLinearMap.le_opNorm R U).trans
      (mul_le_mul hR hU (norm_nonneg U) (mul_nonneg hK (Real.rpow_nonneg hr.le _)))
  have hbound : c * r ^ beta * ‖W‖ ≤ ‖H‖ + K * r ^ (-(N : ℝ)) * M := by
    apply hrow.trans
    calc
      ‖T W‖ = ‖H - R U‖ := by rw [hidentity, add_sub_cancel_right]
      _ ≤ ‖H‖ + ‖R U‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add le_rfl hRnorm
  have he := homogeneousPair_energy_control W H (r ^ beta)
    (K * r ^ (-(N : ℝ)) * M) c (Real.rpow_nonneg hr.le _)
    (by positivity) hc hbound
  have hp : (r ^ beta) ^ 2 = r ^ (2 * beta) := by
    rw [mul_comm (2 : ℝ) beta, Real.rpow_mul hr.le, Real.rpow_ofNat]
  have hq : (r ^ (-(N : ℝ))) ^ 2 = r ^ (-2 * (N : ℝ)) := by
    rw [show -2 * (N : ℝ) = (-(N : ℝ)) * 2 by ring,
      Real.rpow_mul hr.le, Real.rpow_ofNat]
  rw [hp] at he
  convert he using 1
  simp only [mul_pow, hq]
  ring

end DefocusingNLS

end OAI
