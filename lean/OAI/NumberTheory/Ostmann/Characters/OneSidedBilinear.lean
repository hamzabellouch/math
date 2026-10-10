import OAI.NumberTheory.Ostmann.Characters.OneSidedBilinearGram
import OAI.NumberTheory.Ostmann.Characters.OneSidedBilinearRows

namespace OAI

noncomputable section
open Polynomial
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters
attribute [local instance] Classical.propDecidable
variable {ρ κ : Type*} [Fintype ρ] [Fintype κ]

def oneSidedWeightEnergy (N : ℕ) (b : ρ → ℕ → ℝ) (ν : κ → ℝ)
    (W : ρ → ℕ → κ → ℂ) : ℝ :=
  ∑ j, ν j * ∑ x : ρ × Fin N, b x.1 x.2 * ‖W x.1 x.2 j‖^2

def oneSidedCrossBudget (q : κ → ℕ) (cuts : Finset ℝ) (Q N : ℕ) (a : ρ → ℕ)
    (b : ρ → ℕ → ℝ) (ν : κ → ℝ) (W : ρ → ℕ → κ → ℂ) : ℝ :=
  ∑ j, ∑ k, if j = k then 0 else
    ν j * ν k * ((q j*q k : ℕ) * rowCrossVariation cuts Q N a b W j k)

theorem oneSided_bilinear_character_bound
    (q : κ → ℕ) (hq : ∀ j, (q j).Prime) (hinj : Function.Injective q)
    (χ : ∀ j, MulChar (ZMod (q j)) ℂ) (hχ : ∀ j, χ j ≠ 1)
    (Q N : ℕ) (a : ρ → ℕ) (hQ : ∀ j, Q.Coprime (q j))
    (μ : ρ × Fin N → ℝ) (b : ρ → ℕ → ℝ) (ν : κ → ℝ)
    (U : ρ × Fin N → ℂ) (V : κ → ℂ) (W : ρ → ℕ → κ → ℂ)
    (hμ : ∀ x, 0 ≤ μ x) (hmass : ∑ x, μ x ≤ 1)
    (hmajorant : ∀ x : ρ × Fin N, μ x ≤ b x.1 x.2)
    (hν : ∀ j, 0 ≤ ν j) (hU : ∀ x, ‖U x‖ ≤ 1) (hV : ∀ j, ‖V j‖ ≤ 1)
    (cuts : Finset ℝ) :
    ‖oneSidedMean μ ν U V (rowCharacterKernel q χ Q N a W)‖^2 ≤
      priorMaxAtom ν * oneSidedWeightEnergy N b ν W +
        oneSidedCrossBudget q cuts Q N a b ν W := by
  have hb (x : ρ × Fin N) : 0 ≤ b x.1 x.2 := (hμ x).trans (hmajorant x)
  have hmax : 0 ≤ priorMaxAtom ν := by unfold priorMaxAtom; positivity
  apply (oneSided_bilinear_gram_bound μ (fun x : ρ × Fin N => b x.1 x.2)
    ν U V (rowCharacterKernel q χ Q N a W) hμ hmass hmajorant hν hU hV).trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hmax
    unfold oneSidedWeightEnergy
    apply Finset.sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_left _ (hν j)
    apply Finset.sum_le_sum
    intro x hx
    apply mul_le_mul_of_nonneg_left _ (hb x)
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    let : Fact (q j).Prime := ⟨hq j⟩
    unfold rowCharacterKernel primeCharacterKernel
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (norm_character_le_one (χ j) _) (norm_nonneg (W x.1 x.2 j))
  · unfold oneSidedCrossBudget
    apply Finset.sum_le_sum
    intro j hj
    apply Finset.sum_le_sum
    intro k hk
    by_cases heq : j = k
    · simp [heq]
    · simp only [ite_eq_right heq]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hν j) (hν k))
      exact characterGram_rows_bound q hq χ hχ Q N a hQ b W j k
        (fun he => heq (hinj he)) cuts

theorem oneSided_bilinear_polynomial_bound
    {σ τ : Type*} [Fintype σ] [Fintype τ]
    (supports : σ → ℝ[X]) (arguments : τ → ℝ[X])
    (q : κ → ℕ) (hq : ∀ j, (q j).Prime) (hinj : Function.Injective q)
    (χ : ∀ j, MulChar (ZMod (q j)) ℂ) (hχ : ∀ j, χ j ≠ 1)
    (Q N : ℕ) (a : ρ → ℕ) (hQ : ∀ j, Q.Coprime (q j))
    (μ : ρ × Fin N → ℝ) (b : ρ → ℕ → ℝ) (ν : κ → ℝ)
    (U : ρ × Fin N → ℂ) (V : κ → ℂ) (W : ρ → ℕ → κ → ℂ)
    (hμ : ∀ x, 0 ≤ μ x) (hmass : ∑ x, μ x ≤ 1)
    (hmajorant : ∀ x : ρ × Fin N, μ x ≤ b x.1 x.2)
    (hν : ∀ j, 0 ≤ ν j) (hU : ∀ x, ‖U x‖ ≤ 1) (hV : ∀ j, ‖V j‖ ≤ 1) :
    ‖oneSidedMean μ ν U V (rowCharacterKernel q χ Q N a W)‖^2 ≤
      priorMaxAtom ν * oneSidedWeightEnergy N b ν W +
        oneSidedCrossBudget q (polynomialSupportCuts supports arguments) Q N a b ν W :=
  oneSided_bilinear_character_bound q hq hinj χ hχ Q N a hQ μ b ν U V W
    hμ hmass hmajorant hν hU hV _

end Ostmann.Characters

end

end OAI
