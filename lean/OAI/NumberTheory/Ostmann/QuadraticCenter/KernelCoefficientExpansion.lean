import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCoefficientBasic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem kernelCoefficient_character_sum {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (ε : ℕ → ℤ) (k : ℕ) (u : ℤ) :
    (∑ s ∈ primeProductSamples P k, kernelCoefficient P ε k s*(jacobiSym u s : ℂ)) =
      (distinctSignAverage P (fun p => ε p*jacobiSym u p) k : ℂ) := by
  classical
  let a : ℝ := (k.factorial : ℝ)/(P.card : ℝ)^k
  calc
    _ = (a : ℂ)*∑ s ∈ primeProductSamples P k,
        (∏ p ∈ s.primeFactors, (ε p : ℂ))*(jacobiSym u s : ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [kernelCoefficient, ite_eq_left hs]
      dsimp [a]
      ring
    _ = (a : ℂ)*∑ U ∈ P.powersetCard k,
        (∏ p ∈ U, (ε p : ℂ))*(jacobiSym u (∏ p ∈ U, p) : ℂ) := by
      rw [sum_primeProductSamples hP]
      congr 1
      apply Finset.sum_congr rfl
      intro U hU
      have hsub := (Finset.mem_powersetCard.mp hU).1
      rw [Nat.primeFactors_prod (fun p hp => hP p (hsub hp))]
    _ = (a : ℂ)*∑ U ∈ P.powersetCard k, ∏ p ∈ U, ((ε p*jacobiSym u p : ℤ) : ℂ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro U hU
      have hsub := (Finset.mem_powersetCard.mp hU).1
      rw [jacobi_finset_prod_right U (fun p : ℕ => p) (fun p hp => (hP p (hsub hp)).ne_zero),
        Int.cast_prod, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      rw [Int.cast_mul]
    _ = _ := by
      unfold distinctSignAverage
      push_cast
      dsimp [a]
      push_cast
      ring

end Ostmann.QuadraticCenter

end

end OAI
