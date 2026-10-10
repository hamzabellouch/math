import OAI.NumberTheory.Ostmann.QuadraticSieve.SignedQuadraticSieve
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticAmplificationBias
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticKernelDecomposition

namespace OAI

/-! # Quantitative kernel counting from a shared character bias -/

namespace Ostmann

open scoped BigOperators Classical

/-- Heath-Brown's quadratic large sieve bounds the number of signed
squarefree kernels with a common amplified character bias. -/
theorem quadratic_biased_kernel_count (sieve : PublishedQuadraticLargeSieve)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (k Z M : ℕ) (e : ℕ → ℂ)
      (U : Finset ℤ) (c : ℝ),
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) → (∀ p ∈ P, p ≤ Z) →
      (∀ p ∈ P, ‖e p‖ ≤ 1) → 0 < P.card → 1 ≤ k → 1 ≤ Z → 1 ≤ M →
      0 ≤ c → 0 < c ^ k - (k : ℝ) ^ 2 / P.card →
      U ⊆ signedSquarefreeRange M →
      (∀ u ∈ U, c ≤ ‖quadraticPrimeMean P e u‖) →
      (U.card : ℝ) ≤ C * ((M : ℝ) * Z ^ k) ^ ε * ((M : ℝ) + Z ^ k) *
        ((k.factorial : ℝ) / (P.card : ℝ) ^ k) /
          (c ^ k - (k : ℝ) ^ 2 / P.card) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := quadratic_kernel_count sieve ε hε
  refine ⟨C, hC, ?_⟩
  intro P k Z M e U c hP hodd hZ he hcard hk hZ1 hM hc hpos hU hbias
  have htest (u : ℤ) (hu : u ∈ U) :=
    quadratic_amplification_lower P k Z hk hP hodd hZ e he hcard u c hc (hbias u hu)
  have hb := hbound M (Z ^ k) (quadraticAmplifiedCoefficients P k e) U
    (c ^ k - (k : ℝ) ^ 2 / P.card) hM (Nat.one_le_pow _ _ hZ1) hpos hU htest
  have henergy := quadratic_amplification_energy P k (Z ^ k) e hP he hcard
  change quadraticSieveEnergy (Z ^ k) (quadraticAmplifiedCoefficients P k e) ≤ _ at henergy
  apply hb.trans
  have hfactor : 0 ≤ C * ((M : ℝ) * (Z ^ k : ℕ)) ^ ε * ((M : ℝ) + (Z ^ k : ℕ)) := by
    positivity
  have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left henergy hfactor)
    (sq_nonneg (c ^ k - (k : ℝ) ^ 2 / P.card))
  simpa only [Nat.cast_pow] using h

/-- The squarefree kernels of the affine values lie in the range
determined by the interval, denominator and numerator. -/
theorem affine_kernel_image_subset (S : Finset ℤ) (X m : ℕ) (h : ℤ)
    (kernel : ℤ → ℤ) (root : ℤ → ℕ)
    (hX : ∀ x ∈ S, |x| ≤ X)
    (hkernel : ∀ x ∈ S, kernel x ≠ 0 ∧ 0 < root x ∧ Squarefree (kernel x).natAbs ∧
      kernel x * (root x : ℤ) ^ 2 = (m : ℤ) * x - h) :
    S.image kernel ⊆ signedSquarefreeRange (m * X + h.natAbs) := by
  intro u hu
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨hu, ht, hsf, heq⟩ := hkernel x hx
  exact affine_kernel_mem_range hu ht hsf heq (hX x hx)

end Ostmann

end OAI
