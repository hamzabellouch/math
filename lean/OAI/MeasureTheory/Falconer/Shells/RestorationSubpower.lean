import OAI.MeasureTheory.Falconer.Shells.ActualRestorationBound

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ENNReal

theorem restoration_polynomial_bound (H : ℕ) {e : ℝ} (he : 0 < e) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((4*(N:ℝ)+1)^(2*H+1)*((N:ℝ)+1)*(((N:ℝ)+1)^3+1)) ≤ ((2:ℝ)^N)^e := by
  obtain ⟨N₁,h₁⟩ := fixed_constant_absorbed (half_pos he) 2
  obtain ⟨N₂,h₂⟩ := fixed_polynomial_subpower (2*H+5) (half_pos he)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN
  have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hb : (N:ℝ)+1 ≤ 4*(N:ℝ)+1 := by linarith
  have hpow : ((N:ℝ)+1)^3+1 ≤ 2*(4*(N:ℝ)+1)^3 := by nlinarith [pow_le_pow_left₀ (by positivity) hb 3]
  calc
    _ ≤ (4*(N:ℝ)+1)^(2*H+1)*(4*(N:ℝ)+1)*(2*(4*(N:ℝ)+1)^3) := by gcongr
    _ = 2*(4*(N:ℝ)+1)^(2*H+5) := by
      rw [show 2*H+5 = (2*H+1)+1+3 by omega,pow_add,pow_add,pow_one]
      ring
    _ ≤ ((2:ℝ)^N)^(e/2)*((2:ℝ)^N)^(e/2) :=
      mul_le_mul (h₁ N ((le_max_left _ _).trans hN)) (h₂ N ((le_max_right _ _).trans hN)) (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

theorem restorationArcBound_decay (H : ℕ) {lam sig : ℝ} (he : 0 < lam+sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      restorationArcBound N H lam sig ≤ ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig)/2)) := by
  obtain ⟨N₀,h₀⟩ := restoration_polynomial_bound H (half_pos he)
  refine ⟨N₀,?_⟩
  intro N hN
  have hp : 0 < (2:ℝ)^N := by positivity
  have hh := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (h₀ N hN)
    (Real.rpow_nonneg hp.le (-(lam+sig))))
  have hr : ((2:ℝ)^N)^((lam+sig)/2)*((2:ℝ)^N)^(-(lam+sig)) = ((2:ℝ)^N)^(-(lam+sig)/2) := by
    rw [← Real.rpow_add hp]; congr 1; ring
  rw [hr] at hh
  rw [ENNReal.ofReal_mul (by positivity)] at hh
  have hc : ENNReal.ofReal ((4*(N:ℝ)+1)^(2*H+1)*((N:ℝ)+1)*(((N:ℝ)+1)^3+1)) =
      (((4*N+1)^(2*H+1):ℕ):ENNReal)*((N+1:ℕ):ENNReal)*(((N+1)^3+1:ℕ):ENNReal) := by
    norm_cast
  rw [hc] at hh
  exact hh

theorem restorationDiscardBound_decay (H : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      restorationDiscardBound N H lam ≤ ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ))+
        ENNReal.ofReal (((2:ℝ)^N)^(-lam/2)) := by
  obtain ⟨N₀,h₀⟩ := fixed_polynomial_subpower (2*H+1) (half_pos hlam)
  refine ⟨N₀,?_⟩
  intro N hN
  apply add_le_add_right
  have hp : 0 < (2:ℝ)^N := by positivity
  have hh := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (h₀ N hN) (Real.rpow_nonneg hp.le (-lam)))
  have hr : ((2:ℝ)^N)^(lam/2)*((2:ℝ)^N)^(-lam) = ((2:ℝ)^N)^(-lam/2) := by
    rw [← Real.rpow_add hp]; congr 1; ring
  rw [hr] at hh
  rw [ENNReal.ofReal_mul (by positivity)] at hh
  have hc : ENNReal.ofReal ((4*(N:ℝ)+1)^(2*H+1)) = (((4*N+1)^(2*H+1):ℕ):ENNReal) := by norm_cast
  rw [hc] at hh
  exact hh

end PlanarFalconer

end OAI
