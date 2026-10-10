import OAI.MeasureTheory.Falconer.Recursion.RelativeScaleBudget

namespace OAI

/-! # Uniform comparison of contact-profile losses with the middle angular scale -/

namespace Falconer

theorem dyadic_rpow_div_depth {N : ℕ} (hN : 0 < N) (κ : ℝ) :
    ((2:ℝ)^N)^(κ/(N:ℝ)) = (2:ℝ)^κ := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  field_simp

theorem inverse_dyadic_neg_power (M : ℕ) (ε : ℝ) :
    (1/(2:ℝ)^M)^(-ε) = ((2:ℝ)^M)^ε := by
  rw [one_div,Real.inv_rpow (by positivity),Real.rpow_neg (by positivity),inv_inv]

theorem contact_loss_le (d : ℕ) {τ γ Δ lam : ℝ}
    (hτ : 0 ≤ τ) (hγΔ : γ ≤ Δ) (hlam : lam ≤ τ*γ) :
    τ*γ+τ*Δ+2*((d:ℝ)+1)*lam ≤ ((2*(d:ℝ)+4)*τ)*Δ := by
  have hγ : τ*γ ≤ τ*Δ := mul_le_mul_of_nonneg_left hγΔ hτ
  have hlam' : 2*((d:ℝ)+1)*lam ≤ 2*((d:ℝ)+1)*(τ*Δ) :=
    mul_le_mul_of_nonneg_left (hlam.trans hγ) (by positivity)
  nlinarith

theorem contact_loss_relative_budget {d : ℕ} {τ γ Δ lam ε : ℝ} {N M : ℕ}
    (hτ : 0 ≤ τ) (hγΔ : γ ≤ Δ) (hlam : lam ≤ τ*γ)
    (hsmall : (2*(d:ℝ)+4)*τ ≤ ε/2)
    (hwidth : (N:ℝ)*Δ ≤ 2*(M:ℝ)) :
    (N:ℝ)*(τ*γ+τ*Δ+2*((d:ℝ)+1)*lam) ≤ (M:ℝ)*ε := by
  have hsum := contact_loss_le d hτ hγΔ hlam
  have hc : 0 ≤ (2*(d:ℝ)+4)*τ := by positivity
  calc
    _ ≤ (N:ℝ)*(((2*(d:ℝ)+4)*τ)*Δ) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg N)
    _ = ((N:ℝ)*Δ)*((2*(d:ℝ)+4)*τ) := by ring
    _ ≤ (2*(M:ℝ))*((2*(d:ℝ)+4)*τ) := mul_le_mul_of_nonneg_right hwidth hc
    _ ≤ (2*(M:ℝ))*(ε/2) := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = _ := by ring

theorem eventually_contact_frostman_coefficient (d : ℕ) {τ γ ε : ℝ}
    (hτ : 0 < τ) (hγ : 0 < γ) (hsmall : (2*(d:ℝ)+4)*τ ≤ ε/2)
    (C κ : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 0 < N → ∀ M : ℕ, ∀ Δ lam : ℝ,
      γ ≤ Δ → lam ≤ τ*γ → (N:ℝ)*Δ ≤ 2*(M:ℝ) →
      C*((2:ℝ)^N)^(τ*Δ+κ/(N:ℝ)+2*((d:ℝ)+1)*lam) ≤ (1/(2:ℝ)^M)^(-ε) := by
  obtain ⟨N₀,hN₀⟩ := eventually_relative_scale_constant (mul_pos hτ hγ) (C*(2:ℝ)^κ)
  refine ⟨N₀,?_⟩
  intro N hN hNp M Δ lam hγΔ hlam hwidth
  have hbudget := contact_loss_relative_budget hτ.le hγΔ hlam hsmall hwidth
  have hh := hN₀ N hN M (τ*Δ+2*((d:ℝ)+1)*lam) ε (by nlinarith [hbudget])
  rw [inverse_dyadic_neg_power]
  apply le_trans ?_ hh
  have he : τ*Δ+κ/(N:ℝ)+2*((d:ℝ)+1)*lam =
      κ/(N:ℝ)+(τ*Δ+2*((d:ℝ)+1)*lam) := by ring
  rw [he,Real.rpow_add (by positivity),dyadic_rpow_div_depth hNp]
  ring_nf
  exact le_rfl

theorem eventually_contact_outer_coefficient (d : ℕ) {τ γ : ℝ}
    (hτ : 0 < τ) (hγ : 0 < γ) (C κ : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 0 < N → ∀ Δ lam : ℝ,
      γ ≤ Δ → lam ≤ τ*γ →
      C*((2:ℝ)^N)^(τ*Δ+κ/(N:ℝ)+2*((d:ℝ)+1)*lam) ≤
        ((2:ℝ)^N)^(((2*(d:ℝ)+4)*τ)*Δ) := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed (mul_pos hτ hγ) (C*(2:ℝ)^κ)
  refine ⟨N₀,?_⟩
  intro N hN hNp Δ lam hγΔ hlam
  have hR : 0 < (2:ℝ)^N := by positivity
  have he : τ*Δ+κ/(N:ℝ)+2*((d:ℝ)+1)*lam =
      κ/(N:ℝ)+(τ*Δ+2*((d:ℝ)+1)*lam) := by ring
  calc
    _ = (C*(2:ℝ)^κ)*((2:ℝ)^N)^(τ*Δ+2*((d:ℝ)+1)*lam) := by
      rw [he,Real.rpow_add hR,dyadic_rpow_div_depth hNp]
      ring
    _ ≤ ((2:ℝ)^N)^(τ*γ)*((2:ℝ)^N)^(τ*Δ+2*((d:ℝ)+1)*lam) :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
    _ = ((2:ℝ)^N)^(τ*γ+τ*Δ+2*((d:ℝ)+1)*lam) := by
      rw [← Real.rpow_add hR]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
      (contact_loss_le d hτ.le hγΔ hlam)

theorem middle_scale_power_decay {N M : ℕ} {Δ gain : ℝ}
    (hgain : 0 ≤ gain) (hwidth : (N:ℝ)*Δ ≤ 2*(M:ℝ)) :
    (1/(2:ℝ)^M)^gain ≤ ((2:ℝ)^N)^(-gain*Δ/2) := by
  have he : (1/(2:ℝ)^M)^gain = ((2:ℝ)^M)^(-gain) := by
    rw [one_div,Real.inv_rpow (by positivity),Real.rpow_neg (by positivity)]
  rw [he]
  apply dyadic_relative_scale_bound M N
  have hh := mul_le_mul_of_nonneg_left hwidth hgain
  nlinarith

end Falconer

end OAI
