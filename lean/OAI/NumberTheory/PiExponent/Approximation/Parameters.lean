import Mathlib

namespace OAI

namespace PiExponent

theorem exists_rational_parameters (ν : ℝ) (hν : 2 < ν) :
    ∃ θ A B C : ℚ,
      0 < (θ : ℝ) ∧ (θ : ℝ) < A ∧ (A : ℝ) < B ∧ (B : ℝ) < 1 ∧
      ν * ((A : ℝ) - θ) > 1 - θ ∧
      1 < (C : ℝ) ∧ (B : ℝ) < 1 / C ∧
      (B : ℝ) < C * θ ∧ (C : ℝ) * θ < 1 := by
  have hνpos : 0 < ν := by linarith
  have hdiv : 1 / ν < (1 / 2 : ℝ) :=
    (div_lt_iff₀ hνpos).2 (by linarith)
  obtain ⟨b, hbl, hbu⟩ := exists_rat_btwn (show (1 / 2 : ℝ) < 1 - 1 / ν by linarith)
  have hbpos : 0 < (b : ℝ) := by linarith
  have hb1 : (b : ℝ) < 1 := by
    have := one_div_pos.mpr hνpos
    linarith
  have hνb : ν * (b : ℝ) < ν - 1 := calc
    _ < ν * (1 - 1 / ν) := mul_lt_mul_of_pos_left hbu hνpos
    _ = ν - 1 := by field_simp
  have hcoeff : 0 < ν * (1 - (b : ℝ)) - 1 := by nlinarith
  have hδtop : 0 < min (1 : ℝ) ((2 * (b : ℝ) - 1) / ((b : ℝ) * b)) :=
    lt_min (by norm_num) (div_pos (by linarith) (mul_pos hbpos hbpos))
  obtain ⟨δ, hδpos, hδtop⟩ := exists_rat_btwn hδtop
  have hδ1 : (δ : ℝ) < 1 := lt_of_lt_of_le hδtop (min_le_left _ _)
  have hδsmall : (δ : ℝ) < (2 * (b : ℝ) - 1) / ((b : ℝ) * b) :=
    lt_of_lt_of_le hδtop (min_le_right _ _)
  have hδprod : (δ : ℝ) * ((b : ℝ) * b) < 2 * (b : ℝ) - 1 :=
    (lt_div_iff₀ (mul_pos hbpos hbpos)).mp hδsmall
  let θ : ℚ := 1 - δ
  let A : ℚ := 1 - b * δ
  have hθcast : (θ : ℝ) = 1 - (δ : ℝ) := by simp [θ]
  have hAcast : (A : ℝ) = 1 - (b : ℝ) * δ := by simp [A]
  have hθpos : 0 < (θ : ℝ) := by rw [hθcast]; linarith
  have hθA : (θ : ℝ) < A := by
    rw [hθcast, hAcast]
    nlinarith [mul_pos (sub_pos.mpr hb1) hδpos]
  have hApos : 0 < (A : ℝ) := lt_trans hθpos hθA
  have hA1 : (A : ℝ) < 1 := by
    rw [hAcast]
    nlinarith [mul_pos hbpos hδpos]
  have hAsq : (A : ℝ) ^ 2 < θ := by
    rw [hAcast, hθcast]
    nlinarith [mul_pos hδpos (sub_pos.mpr hδprod)]
  have hgap : 1 - (θ : ℝ) < ν * ((A : ℝ) - θ) := by
    rw [hAcast, hθcast]
    nlinarith [mul_pos hcoeff hδpos]
  have hCinterval : (A : ℝ) / θ < 1 / A := by
    apply (div_lt_div_iff₀ hθpos hApos).2
    nlinarith
  obtain ⟨C, hClo, hChi⟩ := exists_rat_btwn hCinterval
  have hC1 : 1 < (C : ℝ) := by
    have : (1 : ℝ) < (A : ℝ) / θ := (lt_div_iff₀ hθpos).2 (by simpa using hθA)
    exact lt_trans this hClo
  have hCpos : 0 < (C : ℝ) := by linarith
  have hACθ : (A : ℝ) < (C : ℝ) * θ := (div_lt_iff₀ hθpos).mp hClo
  have hCA : (C : ℝ) * A < 1 := (lt_div_iff₀ hApos).mp hChi
  have hAinvC : (A : ℝ) < 1 / C := (lt_div_iff₀ hCpos).2 (by nlinarith)
  have hCθ1 : (C : ℝ) * θ < 1 := by nlinarith [mul_lt_mul_of_pos_left hθA hCpos]
  have hBinterval : (A : ℝ) < min (1 / (C : ℝ)) ((C : ℝ) * θ) :=
    lt_min hAinvC hACθ
  obtain ⟨B, hBlo, hBhi⟩ := exists_rat_btwn hBinterval
  have hBinv : (B : ℝ) < 1 / C := lt_of_lt_of_le hBhi (min_le_left _ _)
  have hBCθ : (B : ℝ) < (C : ℝ) * θ := lt_of_lt_of_le hBhi (min_le_right _ _)
  exact ⟨θ, A, B, C, hθpos, hθA, hBlo, lt_trans hBCθ hCθ1,
    hgap, hC1, hBinv, hBCθ, hCθ1⟩

theorem exists_eta_preserving_exponent_gap
    (nu theta A : ℝ) (hnu : 2 < nu) (hA : 0 < A)
    (hgap : 1 - theta < nu * (A - theta)) :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      0 < nu * (A * (1 - eta) - theta) - (1 - theta) := by
  let gap : ℝ := nu * (A - theta) - (1 - theta)
  have hgap_pos : 0 < gap := by dsimp [gap]; linarith
  have hnu_pos : 0 < nu := by linarith
  have hden_pos : 0 < 2 * nu * A := by positivity
  let eta : ℝ := min (1 / 2) (gap / (2 * nu * A))
  have heta_pos : 0 < eta := by
    dsimp [eta]
    exact lt_min (by norm_num) (div_pos hgap_pos hden_pos)
  have heta_half : eta ≤ 1 / 2 := min_le_left _ _
  have heta_lt_one : eta < 1 := by linarith
  have heta_gap : eta ≤ gap / (2 * nu * A) := min_le_right _ _
  have hscaled : eta * (2 * nu * A) ≤ gap :=
    (le_div_iff₀ hden_pos).mp heta_gap
  refine ⟨eta, heta_pos, heta_lt_one, ?_⟩
  dsimp [gap] at hgap_pos hscaled
  nlinarith

structure Parameters (ν : ℝ) where
  theta : ℚ
  A : ℚ
  B : ℚ
  C : ℚ
  eta : ℝ
  theta_pos : 0 < (theta : ℝ)
  theta_lt_A : (theta : ℝ) < A
  A_lt_B : (A : ℝ) < B
  B_lt_one : (B : ℝ) < 1
  approximation_gap : 1 - (theta : ℝ) < ν * ((A : ℝ) - theta)
  one_lt_C : 1 < (C : ℝ)
  B_lt_inv_C : (B : ℝ) < 1 / C
  B_lt_C_theta : (B : ℝ) < (C : ℝ) * theta
  C_theta_lt_one : (C : ℝ) * theta < 1
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  gap_pos : 0 < ν * ((A : ℝ) * (1 - eta) - theta) - (1 - theta)

theorem exists_parameters (ν : ℝ) (hν : 2 < ν) : Nonempty (Parameters ν) := by
  obtain ⟨theta, A, B, C, htheta, hthetaA, hAB, hB, hgap, hC, hBinv, hBC, hCtheta⟩ :=
    exists_rational_parameters ν hν
  obtain ⟨eta, heta, heta1, hgapeta⟩ := exists_eta_preserving_exponent_gap
    ν theta A hν (lt_trans htheta hthetaA) hgap
  exact ⟨⟨theta, A, B, C, eta, htheta, hthetaA, hAB, hB, hgap, hC,
    hBinv, hBC, hCtheta, heta, heta1, hgapeta⟩⟩

namespace Parameters

variable {ν : ℝ} (p : Parameters ν)

theorem A_pos : 0 < (p.A : ℝ) := lt_trans p.theta_pos p.theta_lt_A

theorem B_pos : 0 < (p.B : ℝ) := lt_trans p.A_pos p.A_lt_B

theorem C_pos : 0 < (p.C : ℝ) := lt_trans zero_lt_one p.one_lt_C

theorem A_lt_one : (p.A : ℝ) < 1 := lt_trans p.A_lt_B p.B_lt_one

theorem theta_lt_one : (p.theta : ℝ) < 1 := lt_trans p.theta_lt_A p.A_lt_one

theorem CB_lt_one : (p.C : ℝ) * p.B < 1 := by
  have h := (lt_div_iff₀ p.C_pos).mp p.B_lt_inv_C
  simpa only [mul_comm] using h

theorem one_lt_C_theta_div_B : 1 < (p.C : ℝ) * p.theta / p.B := by
  apply (lt_div_iff₀ p.B_pos).2
  simpa using p.B_lt_C_theta

theorem one_lt_B_div_A : 1 < (p.B : ℝ) / p.A := by
  apply (lt_div_iff₀ p.A_pos).2
  simpa using p.A_lt_B

end Parameters

end PiExponent

end OAI
