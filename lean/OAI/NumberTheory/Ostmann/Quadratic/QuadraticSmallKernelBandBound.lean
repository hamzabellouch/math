import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallKernelWindow
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticUniformBilinear

namespace OAI

/-! # The literal small-kernel middle correction is bounded by shorter matrices -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_small_kernel_band_bound (ρ : 𝓢(ℝ, ℂ)) (M U V : ℝ)
    (E B N D L : ℕ) (hE : 1 ≤ E) (hB : 0 < B) (hD : 0 < D)
    (v w : ℕ → ℂ) (K₁ K₂ : ℕ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hK₁ : ∀ i ≤ Nat.log 2 (2 * N), 0 ≤ K₁ i)
    (hK₂ : ∀ j ≤ Nat.log 2 (2 * N), 0 ≤ K₂ j)
    (h₁ : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i) (K₁ i))
    (h₂ : ∀ j ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ j) (K₂ j))
    (hcost : ∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) v) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) w) ≤ T) :
    ‖∑ d ∈ (Finset.Ioc D (2 * D)).filter
        (fun d : ℕ => U < (E * d : ℕ) ∧ (E * d : ℕ) ≤ V),
      ∑ b ∈ (oddSquarefreeRange (2 * B)).filter (fun b => B ≤ b),
        ((((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) / (Real.sqrt b : ℂ)) *
          quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ))
            (quadraticSmallScale M b / (E * d : ℕ)) L) *
          quadraticDivisorBilinear (2 * N) (2 * N) d v w b‖ ≤
      (((2 * L + 1) * quadraticSmallFourierBound ρ) / ((D : ℝ) * Real.sqrt B)) *
        ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) := by
  let S := (Finset.Ioc D (2 * D)).filter
    (fun d : ℕ => U < (E * d : ℕ) ∧ (E * d : ℕ) ≤ V)
  let R := (oddSquarefreeRange (2 * B)).filter (fun b => B ≤ b)
  let C := ((2 * L + 1) * quadraticSmallFourierBound ρ) / ((D : ℝ) * Real.sqrt B)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (mul_nonneg (by positivity) (quadraticSmallFourierBound_nonneg ρ)) (by positivity)
  have hbound := quadratic_bilinear_uniform_bound (2 * B) (2 * N) (2 * N) D v w
    K₁ K₂ T hT hK₁ hK₂ h₁ h₂ hcost
  calc
    _ ≤ ∑ d ∈ S, ∑ b ∈ R, C * ‖quadraticDivisorBilinear (2 * N) (2 * N) d v w b‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d hd
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b hb
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (quadratic_small_kernel_fourier_weight ρ _ L hE hD hB
          (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).1.le (Finset.mem_filter.mp hb).2)
        (norm_nonneg _)
    _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
        C * ‖quadraticDivisorBilinear (2 * N) (2 * N) d v w b‖ := by
      apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
        (fun d _ _ => Finset.sum_nonneg (fun b _ => mul_nonneg hC (norm_nonneg _)))).trans
      exact Finset.sum_le_sum (fun d _ =>
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
          (fun b _ _ => mul_nonneg hC (norm_nonneg _)))
    _ = C * (∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
        ‖quadraticDivisorBilinear (2 * N) (2 * N) d v w b‖) := by simp only [Finset.mul_sum]
    _ ≤ C * (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) * (Nat.log 2 (2 * N) + 1) * T) :=
      mul_le_mul_of_nonneg_left hbound hC
    _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; ring

end Ostmann

end OAI
