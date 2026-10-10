import OAI.NumberTheory.Ostmann.QuadraticSieveMainConvolutionSums

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped ArithmeticFunction.Moebius

theorem mainConvolution_difference_eq_tail (K Δ : ℕ) (hΔ : 0 < Δ) (ho : Odd Δ)
    (f : ℕ → ℂ) :
    (∑ e ∈ Δ.divisors, (μ e : ℂ) * ∑ b ∈ oddSquarefreeUpTo K, f (e * b)) -
      (∑ u ∈ Δ.divisors, (μ u : ℂ) * ∑ v ∈ oddSquarefreeUpTo K,
        if Nat.Coprime v Δ then f (u ^ 2 * v) else 0) =
      ∑ w ∈ Finset.Ioc K (K * Δ ^ 2), (mainRemainder K Δ w : ℂ) * f w := by
  have hD : Δ ≤ Δ ^ 2 := by nlinarith
  rw [truncatedMainAlpha_sum K Δ (K * Δ ^ 2) hΔ ho (Nat.mul_le_mul_left K hD),
    truncatedMainBeta_sum K Δ (K * Δ ^ 2) hΔ ho le_rfl,
    ← Finset.sum_sub_distrib]
  calc
    _ = ∑ w ∈ Finset.Icc 1 (K * Δ ^ 2), (mainRemainder K Δ w : ℂ) * f w := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [mainRemainder, Int.cast_sub, sub_mul]
    _ = _ := by
      symm
      apply Finset.sum_subset
      · intro w hw
        obtain ⟨hw1, hw2⟩ := Finset.mem_Ioc.mp hw
        exact Finset.mem_Icc.mpr ⟨by omega, hw2⟩
      · intro w hw hnot
        have hwK : w ≤ K := by
          have hwL := (Finset.mem_Icc.mp hw).2
          by_contra hn
          exact hnot (Finset.mem_Ioc.mpr ⟨by omega, hwL⟩)
        rw [mainRemainder_zero_of_le hΔ.ne' hwK]
        simp

end Ostmann.QuadraticSieve

end OAI
