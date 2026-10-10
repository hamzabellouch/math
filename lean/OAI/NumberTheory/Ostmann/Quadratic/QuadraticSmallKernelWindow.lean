import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallKernelScale
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrectionWeights

namespace OAI

/-! # The retained small-kernel Fourier window with its actual reciprocal weights -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def quadraticSmallFourierBound (ρ : 𝓢(ℝ, ℂ)) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 (𝓕 (quadraticSmallSquareTest ρ))

theorem quadraticSmallFourierBound_nonneg (ρ : 𝓢(ℝ, ℂ)) :
    0 ≤ quadraticSmallFourierBound ρ :=
  (norm_nonneg _).trans ((𝓕 (quadraticSmallSquareTest ρ)).norm_le_seminorm ℝ 0)

theorem quadratic_small_window_bound (ρ : 𝓢(ℝ, ℂ)) (X : ℝ) (L : ℕ) :
    ‖quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ)) X L‖ ≤
      (2 * L + 1) * quadraticSmallFourierBound ρ := by
  have hcard : (Finset.Icc (-(L : ℤ)) L).card = 2 * L + 1 := by
    rw [Int.card_Icc]
    omega
  unfold quadraticLatticeWindow
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _n ∈ Finset.Icc (-(L : ℤ)) L, quadraticSmallFourierBound ρ := by
      apply Finset.sum_le_sum
      intro n _
      by_cases hn : n = 0
      · simp only [hn, ite_true, norm_zero]
        exact quadraticSmallFourierBound_nonneg ρ
      · rw [ite_eq_right hn]
        exact (𝓕 (quadraticSmallSquareTest ρ)).norm_le_seminorm ℝ _
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcard]; push_cast; rfl

theorem quadratic_small_kernel_fourier_weight (ρ : 𝓢(ℝ, ℂ)) (X : ℝ) (L : ℕ)
    {E D B d b : ℕ} (hE : 1 ≤ E) (hD : 0 < D) (hB : 0 < B)
    (hd : D ≤ d) (hb : B ≤ b) :
    ‖(((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) /
        (Real.sqrt b : ℂ)) *
        quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ)) X L‖ ≤
      ((2 * L + 1) * quadraticSmallFourierBound ρ) / ((D : ℝ) * Real.sqrt B) := by
  have hd' : D ≤ E * d := hd.trans (le_mul_of_one_le_left (Nat.zero_le d) hE)
  rw [norm_mul]
  calc
    _ ≤ (1 / ((D : ℝ) * Real.sqrt B)) *
        ((2 * L + 1) * quadraticSmallFourierBound ρ) :=
      mul_le_mul (quadratic_moebius_root_weight hD hB hd' hb)
        (quadratic_small_window_bound ρ X L) (norm_nonneg _) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
