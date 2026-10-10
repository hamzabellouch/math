import OAI.MeasureTheory.Falconer.Recursion.FrostmanProfiles
import OAI.MeasureTheory.Falconer.Estimates.RegularizationSubpower
import OAI.MeasureTheory.Falconer.Shells.ShellSummability

namespace OAI

/-! # Polynomial restoration losses and the coarse product-filter cost -/

namespace Falconer
open Filter

theorem eventual_polynomial_decay {a : ℝ} (ha : 0 < a) (C : ℝ) (k : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      C*((N:ℝ)+1)^k*((2:ℝ)^N)^(-a) ≤ ((2:ℝ)^N)^(-a/2) := by
  obtain ⟨N₁,h₁⟩ := Regularization.fixed_constant_absorbed (by positivity : 0 < a/4) C
  obtain ⟨N₂,h₂⟩ := PlanarFalconer.fixed_polynomial_subpower k (by positivity : 0 < a/4)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN
  have hR : 0 < (2:ℝ)^N := by positivity
  have hp : ((N:ℝ)+1)^k ≤ ((2:ℝ)^N)^(a/4) :=
    (pow_le_pow_left₀ (by positivity)
      (by nlinarith [show (0:ℝ) ≤ (N:ℝ) from Nat.cast_nonneg N] : (N:ℝ)+1 ≤ 4*N+1) k).trans
      (h₂ N ((le_max_right _ _).trans hN))
  calc
    _ ≤ (((2:ℝ)^N)^(a/4)*((2:ℝ)^N)^(a/4))*((2:ℝ)^N)^(-a) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (h₁ N ((le_max_left _ _).trans hN)) hp (by positivity) (by positivity)) (by positivity)
    _ = _ := by rw [← Real.rpow_add hR,← Real.rpow_add hR]; congr 1; ring

theorem eventual_partition_shell_decay {β θ : ℝ} (hβ : 0 < β) (hθ : 2*θ ≤ β/64) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ k : ℕ, (k:ℝ) ≤ ((2:ℝ)^N)^θ →
      2*(k:ℝ)^2*((2:ℝ)^N)^(-β/16) ≤ ((2:ℝ)^N)^(-β/32) := by
  obtain ⟨N₀,h₀⟩ := Regularization.fixed_constant_absorbed (by positivity : 0 < β/64) 2
  refine ⟨N₀,?_⟩
  intro N hN k hk
  have hR : 0 < (2:ℝ)^N := by positivity
  have hR1 : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hk2 : (k:ℝ)^2 ≤ ((2:ℝ)^N)^(β/64) := by
    calc
      _ ≤ (((2:ℝ)^N)^θ)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hk 2
      _ = ((2:ℝ)^N)^(2*θ) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hR.le]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR1 hθ
  calc
    _ ≤ (((2:ℝ)^N)^(β/64)*((2:ℝ)^N)^(β/64))*((2:ℝ)^N)^(-β/16) :=
      mul_le_mul_of_nonneg_right (mul_le_mul (h₀ N hN) hk2 (by positivity) (by positivity)) (by positivity)
    _ = _ := by rw [← Real.rpow_add hR,← Real.rpow_add hR]; congr 1; ring

theorem dyadic_scale_power (N : ℕ) (a : ℝ) : ((2:ℝ)^N)^a = (2:ℝ)^(a*(N:ℝ)) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),mul_comm]

theorem summable_scale_decay {a : ℝ} (ha : 0 < a) :
    Summable (fun N : ℕ => ((2:ℝ)^N)^(-a)) := by
  simp_rw [dyadic_scale_power]
  exact PlanarFalconer.summable_dyadic_decay ha

theorem summable_polynomial_scale_decay {a : ℝ} (ha : 0 < a) (C : ℝ) (k : ℕ) :
    Summable (fun N : ℕ => C*((N:ℝ)+1)^k*((2:ℝ)^N)^(-a)) := by
  obtain ⟨N₀,h₀⟩ := eventual_polynomial_decay (half_pos ha) |C| k
  apply (summable_scale_decay (show 0 < a/4 by positivity)).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop N₀] with N hN
  rw [norm_mul,norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ ((N:ℝ)+1)^k),
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  have hh := h₀ N hN
  have hR1 : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  calc
    _ ≤ |C| *((N:ℝ)+1)^k*((2:ℝ)^N)^(-(a/2)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)) (by positivity)
    _ ≤ _ := by
      have he : -(a/2)/2 = -(a/4) := by ring
      simpa only [he] using hh

end Falconer

end OAI
