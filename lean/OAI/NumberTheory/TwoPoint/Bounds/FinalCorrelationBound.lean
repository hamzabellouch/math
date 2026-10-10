import OAI.NumberTheory.TwoPoint.Bounds.FinalErrorScale
import OAI.NumberTheory.TwoPoint.Bounds.QuantitativeCenteringAssembly

namespace OAI

/-! Arithmetic assembly of the centering, endpoint deletion, and retained
spectral estimates at the manuscript's final parameter choice. -/

namespace TwoPointCorrelations

lemma quantitative_deletion_small (L W C : ℝ) (J : ℕ)
    (hL : 1 ≤ L) (hW : 1 ≤ W) (hC : 0 ≤ C)
    (hJ : 60 * (J : ℝ) ≤ Real.log L)
    (hr : Real.exp (-L ^ (9 / 10 : ℝ)) ≤ Real.exp (-(J : ℝ))) :
    (2 : ℝ) ^ J * (C / Real.exp (4 * J) + L ^ (-100 : ℝ) +
      Real.exp (-2 * W * J)) + 2 * Real.exp (-L ^ (9 / 10 : ℝ)) ≤
        (C + 4) * Real.exp (-(J : ℝ)) := by
  obtain ⟨_, hk, hl, hw⟩ := quantitative_small_terms L W J hL hW hJ
  have hc := mul_le_mul_of_nonneg_left hk hC
  have he : (2 : ℝ) ^ J * (C / Real.exp (4 * J)) =
      C * ((2 : ℝ) ^ J * Real.exp (-4 * (J : ℝ))) := by
    rw [show (4 : ℝ) * J = -(-4 * (J : ℝ)) by ring, Real.exp_neg]
    simp only [div_eq_mul_inv, inv_inv]
    ring
  rw [← he] at hc
  nlinarith

lemma reciprocal_cutoff_saving (L W X : ℝ) (A : ℕ)
    (hL : 1 ≤ L) (hW : 1 ≤ W) (hA : A ≠ 0)
    (hX : Real.exp (L ^ A) ≤ X) :
    1 / X ≤ Real.exp (-(primeSupplyCount W L : ℝ)) := by
  have hXp : 0 < X := (Real.exp_pos _).trans_le hX
  have hJ := primeSupplyCount_le_log W L hW hL
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hpow : L ≤ L ^ A := le_self_pow₀ hL hA
  calc
    1 / X ≤ 1 / Real.exp (L ^ A) := one_div_le_one_div_of_le (Real.exp_pos _) hX
    _ = Real.exp (-(L ^ A)) := by rw [Real.exp_neg, one_div]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

lemma correlation_normalized_bound (raw retained F : ℂ)
    (S₀ M η Cret Cdel Ccenter Xinv : ℝ)
    (hS : 0 < S₀) (_hM : 0 ≤ M) (hη : 0 ≤ η)
    (_hretC : 0 ≤ Cret) (hdelC : 0 ≤ Cdel) (hcenterC : 0 ≤ Ccenter)
    (hmass : M / 2 ≤ S₀) (hX : Xinv ≤ η)
    (hret : ‖retained‖ / S₀ ≤ Cret * η)
    (hdel : ‖raw - retained‖ ≤ 2 * M * ((Cdel + 4) * η))
    (hcenter : ‖raw - (S₀ : ℂ) * F‖ ≤
      Ccenter * η * M + S₀ * (2 * η + Xinv)) :
    ‖F‖ ≤ (Cret + 4 * Cdel + 2 * Ccenter + 19) * η := by
  have hr := (div_le_iff₀ hS).mp hret
  have hmc : Ccenter * η * M ≤ 2 * Ccenter * η * S₀ := by
    have hx := mul_le_mul_of_nonneg_left (show M ≤ 2 * S₀ by linarith)
      (mul_nonneg hcenterC hη)
    nlinarith
  have hmd : 2 * M * ((Cdel + 4) * η) ≤
      4 * (Cdel + 4) * η * S₀ := by
    have hx := mul_le_mul_of_nonneg_left (show M ≤ 2 * S₀ by linarith)
      (show 0 ≤ 2 * ((Cdel + 4) * η) by positivity)
    nlinarith
  have ht : ‖(S₀ : ℂ) * F‖ ≤
      ‖raw - (S₀ : ℂ) * F‖ + ‖raw - retained‖ + ‖retained‖ := by
    calc
      _ = ‖raw - (raw - (S₀ : ℂ) * F)‖ := by congr 1; ring
      _ ≤ ‖raw‖ + ‖raw - (S₀ : ℂ) * F‖ := norm_sub_le _ _
      _ ≤ (‖raw - retained‖ + ‖retained‖) + ‖raw - (S₀ : ℂ) * F‖ := by
        gcongr
        calc
          ‖raw‖ = ‖(raw - retained) + retained‖ := by rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      _ = _ := by ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS] at ht
  have hxe := mul_le_mul_of_nonneg_left hX hS.le
  have hf : S₀ * ‖F‖ ≤ S₀ * ((Cret + 4 * Cdel + 2 * Ccenter + 19) * η) := by
    nlinarith
  exact (mul_le_mul_iff_right₀ hS).mp hf

end TwoPointCorrelations

end OAI
