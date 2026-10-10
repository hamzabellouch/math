import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSecondMain
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticOriginalMainTerms

namespace OAI

/-! # The transformed first main term is the original comparison term -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate SchwartzMap

noncomputable def quadraticDualMainCoefficient (M : ℝ) (D q b : ℕ) : ℂ :=
  quadraticGaussMultiplier q *
    (∑ e ∈ (2 * D).divisors, (ArithmeticFunction.moebius e : ℂ) *
      (((M / ((e : ℝ) * Real.sqrt q) * quadraticSecondScale M e q b) : ℝ) : ℂ) *
        ∑ a ∈ ({1, -1, 2, -2} : Finset ℤ),
          (jacobiSym ((e : ℤ) * a) q : ℂ) * quadraticFresnelPhase a /
            (Real.sqrt |(a : ℝ)| : ℂ))

noncomputable def quadraticTransformedFirstMain (M : ℝ) (N D K : ℕ)
    (ρ : 𝓢(ℝ, ℂ)) (b : ℕ → ℂ) : ℂ :=
  ((∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) / 2) *
    ∑ z ∈ quadraticGcdPairs N D, b z.1 * conj (b z.2) *
      ((Nat.totient (quadraticPairKernel z.1 z.2) : ℂ) / quadraticPairKernel z.1 z.2) *
        ∑ v ∈ oddSquarefreeRange K, (jacobiSym (v : ℤ) (quadraticPairKernel z.1 z.2) : ℂ) *
          quadraticDualMainCoefficient M D (quadraticPairKernel z.1 z.2) v

theorem quadratic_transformed_first_main {M : ℝ} (hM : 0 < M)
    (N D K : ℕ) (hD : Odd D) (ρ : 𝓢(ℝ, ℂ)) (b : ℕ → ℂ) :
    quadraticTransformedFirstMain M N D K ρ b =
      ((Real.sqrt M : ℂ) / 2 * ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) *
        quadraticFirstMain N D K b := by
  unfold quadraticTransformedFirstMain quadraticFirstMain
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨hz, _⟩ := Finset.mem_filter.mp hz
  obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hz
  obtain ⟨_, ho₁, hs₁⟩ := Finset.mem_filter.mp h₁
  obtain ⟨_, ho₂, hs₂⟩ := Finset.mem_filter.mp h₂
  have hq := quadraticPairKernel_squarefree hs₁ hs₂
  have hqo := quadraticPairKernel_odd ho₁ ho₂
  have hv : (∑ v ∈ oddSquarefreeRange K,
      (jacobiSym (v : ℤ) (quadraticPairKernel z.1 z.2) : ℂ) *
        quadraticDualMainCoefficient M D (quadraticPairKernel z.1 z.2) v) =
      (Real.sqrt M : ℂ) *
        (∑ e ∈ D.divisors, (ArithmeticFunction.moebius e : ℂ) *
          quadraticRootCharacter (quadraticPairKernel z.1 z.2) e) *
        ∑ v ∈ oddSquarefreeRange K, quadraticRootCharacter (quadraticPairKernel z.1 z.2) v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    have hv₀ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1).1
    unfold quadraticDualMainCoefficient
    rw [quadratic_second_main_coefficient hM hq hqo hD hv₀]
    unfold quadraticRootCharacter
    push_cast
    ring
  rw [hv]
  ring

end Ostmann

end OAI
