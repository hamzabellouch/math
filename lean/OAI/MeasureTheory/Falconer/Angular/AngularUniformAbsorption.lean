import OAI.MeasureTheory.Falconer.Angular.AngularProfileSum
import OAI.MeasureTheory.Falconer.Estimates.RegularizationSubpower

namespace OAI

namespace PlanarFalconer

theorem fixed_linear_subpower (C : ℝ) (hC : 0 ≤ C) {e : ℝ} (he : 0 < e) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, C*(1+2*(N:ℝ)) ≤ ((2:ℝ)^N)^e := by
  obtain ⟨N₁,hN₁⟩ := fixed_constant_absorbed (half_pos he) C
  obtain ⟨N₂,hN₂⟩ := fixed_polynomial_subpower 1 (half_pos he)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN
  have hc := hN₁ N ((le_max_left _ _).trans hN)
  have hp := hN₂ N ((le_max_right _ _).trans hN)
  simp only [pow_one] at hp
  have hlin : 1+2*(N:ℝ) ≤ ((2:ℝ)^N)^(e/2) := by
    have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
    linarith
  calc
    _ ≤ C*((2:ℝ)^N)^(e/2) := mul_le_mul_of_nonneg_left hlin hC
    _ ≤ ((2:ℝ)^N)^(e/2)*((2:ℝ)^N)^(e/2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

theorem angular_ratio_absorption {N : ℕ} {K lam sig C : ℝ}
    (hlam : 0 < lam) (hsig : 0 < sig)
    (hC : C ≤ ((2:ℝ)^N)^(lam+sig)) :
    (C*((2:ℝ)^N)^(K+1000*sig+12*lam))/
        ((2:ℝ)^N)^(K+2000*(lam+sig)) ≤ ((2:ℝ)^N)^(-(lam+sig)) := by
  have hRp : 0 < (2:ℝ)^N := by positivity
  calc
    _ ≤ (((2:ℝ)^N)^(lam+sig)*((2:ℝ)^N)^(K+1000*sig+12*lam))/
        ((2:ℝ)^N)^(K+2000*(lam+sig)) := by gcongr
    _ = ((2:ℝ)^N)^((lam+sig)+(K+1000*sig+12*lam)-(K+2000*(lam+sig))) := by
      rw [← Real.rpow_add hRp,← Real.rpow_sub hRp]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)

end PlanarFalconer

end OAI
