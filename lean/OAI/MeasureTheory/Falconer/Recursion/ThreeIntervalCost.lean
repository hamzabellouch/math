import OAI.MeasureTheory.Falconer.Recursion.ContactLossBudget

namespace OAI

/-! # A uniform power bound for the three local deletions and density pruning -/

namespace Falconer

theorem eventually_three_interval_cost {τ γ L gain : ℝ}
    (hτ : 0 < τ) (hγ : 0 < γ) (hL : 1 ≤ 2*L) (hgain : 2*τ ≤ gain) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : ℕ, ∀ Δ : ℝ, γ ≤ Δ →
      (N:ℝ)*Δ ≤ 2*(M:ℝ) →
      2*((2:ℝ)^N)^(-(2*(L*τ*Δ)))+2*(1/(2:ℝ)^M)^gain+
        4*((2:ℝ)^N)^(-(τ*Δ)) ≤ ((2:ℝ)^N)^(-(τ*γ/2)) := by
  have hη : 0 < τ*γ/2 := by positivity
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hη 8
  refine ⟨N₀,?_⟩
  intro N hN M Δ hγΔ hwidth
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hΔ0 : 0 ≤ Δ := hγ.le.trans hγΔ
  have hbase : τ*γ ≤ τ*Δ := mul_le_mul_of_nonneg_left hγΔ hτ.le
  have houtExp : τ*γ ≤ 2*(L*τ*Δ) := by
    have hh := mul_le_mul_of_nonneg_right hL (mul_nonneg hτ.le hΔ0)
    nlinarith
  have hmidExp : τ*γ ≤ gain*Δ/2 := by
    have hh := mul_le_mul_of_nonneg_right hgain hΔ0
    nlinarith
  have hout : R^(-(2*(L*τ*Δ))) ≤ R^(-(τ*γ)) :=
    Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
  have hmid : (1/(2:ℝ)^M)^gain ≤ R^(-(τ*γ)) :=
    (middle_scale_power_decay (by linarith : 0 ≤ gain) hwidth).trans
      (Real.rpow_le_rpow_of_exponent_le hR1 (by linarith))
  have hdensity : R^(-(τ*Δ)) ≤ R^(-(τ*γ)) :=
    Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
  calc
    _ ≤ 8*R^(-(τ*γ)) := by nlinarith
    _ ≤ R^(τ*γ/2)*R^(-(τ*γ)) :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
    _ = _ := by rw [← Real.rpow_add hR]; congr 1; ring

end Falconer

end OAI
