import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Structure.ArithFrobIntegerGlobalCongruence
import OAI.NumberTheory.SiegelZeros.Structure.QuadraticEigencharacter

namespace OAI

namespace SiegelZeros

open scoped NumberField
open scoped NumberField

namespace WeightedTorusJets

theorem source_quadratic_group_character_with_frobenius
    {K : Type*} [Field K] [NumberField K]
    (a : K) (d : ℚ) (ha : a ^ 2 = algebraMap ℚ K d) (hd : ¬ IsSquare d)
    (σ τ : K ≃ₐ[ℚ] K) (hσ : σ a = -a) (hτ : τ a = a)
    (ν : K →ₐ[ℚ] ℂ) (q : ℕ) (χ : DirichletCharacter ℂ q)
    (hfrob : ∀ p : ℕ, p.Prime → ¬ p ∣ 2 * q → χ p = -1 →
      ((∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - σ • x) ∨
        (∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - (σ * τ) • x))) :
    ∃ ξ : (K ≃ₐ[ℚ] K) →* K,
      (∀ f, f a = ξ f * a) ∧
      (∀ f, ξ f = 1 ∨ ξ f = -1) ∧
      ξ σ = -1 ∧ ξ τ = 1 ∧ ξ (σ * τ) = -1 ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ 2 * q → χ p = -1 →
        ∃ φ : K ≃ₐ[ℚ] K, (φ = σ ∨ φ = σ * τ) ∧
          (∀ (P : Ideal (𝓞 K)) (_ : P.IsPrime),
            P.LiesOver (Ideal.span {(p : ℤ)}) → IsArithFrobAt ℤ φ P) ∧
          ν (ξ φ) = χ p ∧ ∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - φ • x := by
  obtain ⟨ξ, hξ, hrange, hξσ, hξτ, hξστ⟩ := source_quadratic_group_character a d ha hd σ τ hσ hτ
  refine ⟨ξ, hξ, hrange, hξσ, hξτ, hξστ, ?_⟩
  intro p hp hpn hχp
  obtain ⟨φ, hchoice, hφ, hglobal⟩ :=
    exists_source_frobenius_of_global_choice p σ τ (hfrob p hp hpn hχp)
  refine ⟨φ, hchoice, hφ, ?_, hglobal⟩
  rcases hchoice with rfl | rfl <;> simp [hξσ, hξστ, hχp]

end WeightedTorusJets


end SiegelZeros

end OAI
