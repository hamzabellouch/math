import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFrequencyTerm
import OAI.NumberTheory.Ostmann.QuadraticCenter.SquarefreeFrequencyRectangle

namespace OAI

/-! # Exact coefficient expansion of the positive Fourier frequencies -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem quadratic_frequency_expansion {q M : ℕ} [NeZero q]
    (L N : ℕ) (hL : Squarefree L) (hM : 0 < M)
    (χ : DirichletCharacter ℂ M) (hχ : χ.IsQuadratic)
    (g : ZMod q → ℂ) (a : ZMod q) (θ R H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hR : 0 < R) (hH : 0 ≤ H) (hN : 1 ≤ N) (hcut : H * R * q ≤ N)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    (Real.sqrt (R * q) : ℂ)⁻¹ *
      (∑ u ∈ Finset.Icc 1 N, χ (u : ZMod M) * quadraticFrequencyTerm g a θ Φ R u) =
      ∑ P ∈ M.divisors, (ArithmeticFunction.moebius P : ℂ) *
        ∑ s ∈ squarefreeKernelSupport L N,
          (χ (s : ZMod M) * (Real.sqrt (s : ℝ) : ℂ)⁻¹) *
          ∑ v ∈ L.divisors, (χ (v : ZMod M) * (Real.sqrt (v : ℝ) : ℂ)⁻¹) *
            positiveQuadraticMultiples g (a * (v : ZMod q)) θ Φ R v s P := by
  classical
  rw [rectangular_frequency_moebius_expansion L N hL hM χ hχ _
    (fun u hu => quadraticFrequencyTerm_zero_above g a θ Φ R H N u hR hcut hu hΦ)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  have hPpos : 0 < P := Nat.pos_of_mem_divisors hP
  rw [mul_left_comm, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  have hspos := (mem_squarefreeKernelSupport L N s).mp hs |>.1
  rw [← mul_assoc, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have hvpos : 0 < v := Nat.pos_of_mem_divisors hv
  rw [positiveQuadraticMultiples_eq_frequency_cutoff g a θ Φ R H s v P N hR hH hspos hvpos hPpos hN hcut hΦ,
    quadratic_frequency_normalizer q s v R (NeZero.pos q) hspos hvpos hR]
  ring

end Ostmann

end OAI
