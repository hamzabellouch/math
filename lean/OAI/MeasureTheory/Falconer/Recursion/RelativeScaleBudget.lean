import OAI.MeasureTheory.Falconer.Recursion.FrostmanProfiles

namespace OAI

/-! # Uniform constant absorption when passing from the full to the middle scale -/

namespace Falconer

theorem dyadic_relative_scale_bound (N k : ℕ) {α β : ℝ}
    (h : (N:ℝ)*α ≤ (k:ℝ)*β) : ((2:ℝ)^N)^α ≤ ((2:ℝ)^k)^β := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h

theorem eventually_relative_scale_constant {η : ℝ} (hη : 0 < η) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ k : ℕ, ∀ α β : ℝ,
      (N:ℝ)*(η+α) ≤ (k:ℝ)*β →
      C*((2:ℝ)^N)^α ≤ ((2:ℝ)^k)^β := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hη C
  refine ⟨N₀,fun N hN k α β hbudget => ?_⟩
  calc
    _ ≤ ((2:ℝ)^N)^η*((2:ℝ)^N)^α :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
    _ = ((2:ℝ)^N)^(η+α) := (Real.rpow_add (by positivity) _ _).symm
    _ ≤ _ := dyadic_relative_scale_bound N k hbudget

end Falconer

end OAI
