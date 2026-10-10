import OAI.NumberTheory.Ostmann.Construction.HistorySmoothFactor

namespace OAI

/-! # The exponential size of the smooth history factor -/

namespace Ostmann

theorem sqrt_ratio_le_exp (X M Δ C : ℝ) (hM : 0 < M)
    (hbound : X * Real.exp (Δ - C) ≤ M) :
    Real.sqrt (X / M) ≤ Real.exp ((C - Δ) / 2) := by
  have hexp : Real.exp (C - Δ) * Real.exp (Δ - C) = 1 := by
    rw [← Real.exp_add, show C - Δ + (Δ - C) = 0 by ring, Real.exp_zero]
  have hX : X ≤ Real.exp (C - Δ) * M := by
    calc
      X = Real.exp (C - Δ) * (X * Real.exp (Δ - C)) := by
        calc
          _ = X * (Real.exp (C - Δ) * Real.exp (Δ - C)) := by rw [hexp, mul_one]
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
  apply Real.sqrt_le_iff.mpr
  refine ⟨(Real.exp_pos _).le, ?_⟩
  have hsquare : Real.exp ((C - Δ) / 2) ^ 2 = Real.exp (C - Δ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hsquare]
  exact (div_le_iff₀ hM).mpr hX

/-- Leaf moduli obey the bound forced by the giant and sum-bin cutoffs.
Internal cutoff factors are at most one in modulus. -/
def HistorySmoothData.ModuliBound (X Δ C : ℝ) : {n : ℕ} → HistorySmoothData n → Prop
  | _, .leaf M _ cutoff => 0 < M ∧ X * Real.exp (Δ - C) ≤ M ∧ |cutoff| ≤ 1
  | _, .node cutoff left right =>
    |cutoff| ≤ 1 ∧ left.ModuliBound X Δ C ∧ right.ModuliBound X Δ C

theorem HistorySmoothData.bounded_of_moduli {n : ℕ} (h : HistorySmoothData n)
    (X Δ C K : ℝ) (hh : h.ModuliBound X Δ C) :
    h.Bounded X (Real.exp K) (Real.exp (K + (C - Δ) / 2)) := by
  induction h with
  | leaf M s cutoff =>
      refine ⟨hh.2.2, ?_⟩
      calc
        _ ≤ Real.exp ((C - Δ) / 2) * Real.exp K := mul_le_mul_of_nonneg_right
          (sqrt_ratio_le_exp X M Δ C hh.1 hh.2.1) (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
  | node cutoff left right ihL ihR => exact ⟨hh.1, ihL hh.2.1, ihR hh.2.2⟩

theorem smooth_history_pair_exp_le {n : ℕ} (h₁ h₂ : HistorySmoothData n)
    (X Δ C K : ℝ) (ψhat : ℝ → ℂ)
    (hψ : ∀ t, ‖ψhat t‖ ≤ Real.exp K)
    (hh₁ : h₁.ModuliBound X Δ C) (hh₂ : h₂.ModuliBound X Δ C) :
    ‖h₁.value X ψhat * star (h₂.value X ψhat)‖ ≤
      Real.exp (-(2 ^ n : ℕ) * Δ + (2 ^ n : ℕ) * (C + 2 * K)) := by
  have h := smooth_history_pair_norm_le h₁ h₂ X (Real.exp K)
    (Real.exp (K + (C - Δ) / 2)) ψhat (Real.exp_pos _).le (Real.exp_pos _).le hψ
    (h₁.bounded_of_moduli X Δ C K hh₁) (h₂.bounded_of_moduli X Δ C K hh₂)
  apply h.trans_eq
  rw [← Real.exp_nat_mul, Nat.cast_mul, Nat.cast_ofNat]
  congr 1
  ring

/-- The optional Archimedean multiplier contributes only its fixed
exponential bound to Xi. -/
theorem full_smooth_factor_exp_le {n : ℕ} (h₁ h₂ : HistorySmoothData n)
    (X Δ C K κ : ℝ) (ψhat : ℝ → ℂ) (A : ℂ)
    (hψ : ∀ t, ‖ψhat t‖ ≤ Real.exp K) (hA : ‖A‖ ≤ Real.exp κ)
    (hh₁ : h₁.ModuliBound X Δ C) (hh₂ : h₂.ModuliBound X Δ C) :
    ‖A * (h₁.value X ψhat * star (h₂.value X ψhat))‖ ≤
      Real.exp (-(2 ^ n : ℕ) * Δ + ((2 ^ n : ℕ) * (C + 2 * K) + κ)) := by
  rw [norm_mul]
  calc
    _ ≤ Real.exp κ * Real.exp (-(2 ^ n : ℕ) * Δ + (2 ^ n : ℕ) * (C + 2 * K)) :=
      mul_le_mul hA (smooth_history_pair_exp_le h₁ h₂ X Δ C K ψhat hψ hh₁ hh₂)
        (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
