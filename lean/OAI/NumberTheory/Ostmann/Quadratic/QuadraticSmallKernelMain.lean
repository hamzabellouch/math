import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallKernelScale
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticOriginalMainTerms

namespace OAI

/-! # Exact identification of the small-kernel main term -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate SchwartzMap

theorem quadratic_small_main_factor {M : ℝ} {q D b : ℕ}
    (hM : 0 < M) (hq : Odd q) (hD : Odd D) (_hb : 0 < b) (I : ℂ) :
    (quadraticSmallScale M b : ℂ) *
      (((2 * (q * D)).totient : ℂ) / (2 * (q * D) : ℕ)) * I =
        ((Real.sqrt M : ℂ) / 2 * I) * (((q * D).totient : ℂ) / (q * D : ℕ)) /
          (Real.sqrt b : ℂ) := by
  rw [Nat.totient_two_mul_of_odd (hq.mul hD)]
  unfold quadraticSmallScale
  rw [Real.sqrt_div hM.le, Complex.ofReal_div]
  push_cast
  ring

noncomputable def quadraticSmallTransformedMain (M : ℝ) (N D K : ℕ)
    (ρ : 𝓢(ℝ, ℂ)) (v : ℕ → ℂ) : ℂ :=
  ∑ z ∈ quadraticGcdPairs N D, v z.1 * conj (v z.2) *
    ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
      (quadraticSmallScale M b : ℂ) *
        (((2 * (quadraticPairKernel z.1 z.2 * D)).totient : ℂ) /
          (2 * (quadraticPairKernel z.1 z.2 * D) : ℕ)) *
        (∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) * (jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ)

theorem quadratic_small_transformed_main {M : ℝ} (hM : 0 < M)
    (N D K : ℕ) (hD : Odd D) (ρ : 𝓢(ℝ, ℂ)) (v : ℕ → ℂ) :
    quadraticSmallTransformedMain M N D K ρ v =
      ((Real.sqrt M : ℂ) / 2 * (∫ x in Ioi (0 : ℝ), ρ (x ^ 2))) *
        quadraticSecondMain N D K v := by
  unfold quadraticSmallTransformedMain quadraticSecondMain
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨hz, _⟩ := Finset.mem_filter.mp hz
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz
  have hq := quadraticPairKernel_odd (Finset.mem_filter.mp hs).2.1 (Finset.mem_filter.mp ht).2.1
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hb₀ : 0 < b :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1).1
  rw [quadratic_small_main_factor hM hq hD hb₀]
  unfold quadraticRootCharacter
  push_cast
  ring

end Ostmann

end OAI
