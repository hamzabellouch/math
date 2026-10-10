import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport

namespace OAI

namespace SiegelZeros

open scoped NumberField

namespace WeightedTorusJets

theorem isArithFrobAt_of_integer_global_congruence
    {K : Type*} [Field K] [NumberField K]
    (p : ℕ) (σ : K ≃ₐ[ℚ] K)
    (h : ∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - σ • x)
    (Q : Ideal (𝓞 K)) [Q.LiesOver (Ideal.span {(p : ℤ)})] :
    IsArithFrobAt ℤ σ Q := by
  intro x
  change σ • x - x ^ Nat.card (ℤ ⧸ Q.under ℤ) ∈ Q
  rw [← Q.over_def (Ideal.span {(p : ℤ)}), Int.card_ideal_quot]
  have hp : (p : 𝓞 K) ∈ Q := by
    have hle := Ideal.map_le_iff_le_comap.mpr
      (show Ideal.span {(p : ℤ)} ≤ Q.under ℤ from (Q.over_def _).le)
    apply hle
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
    exact Ideal.subset_span (by simp)
  simpa only [neg_sub] using Q.neg_mem (Q.mem_of_dvd (h x) hp)

theorem exists_source_frobenius_of_global_choice
    {K : Type*} [Field K] [NumberField K]
    (p : ℕ) (σ τ : K ≃ₐ[ℚ] K)
    (h : (∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - σ • x) ∨
      (∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - (σ * τ) • x)) :
    ∃ φ : K ≃ₐ[ℚ] K, (φ = σ ∨ φ = σ * τ) ∧
      (∀ (Q : Ideal (𝓞 K)) (_ : Q.IsPrime),
        Q.LiesOver (Ideal.span {(p : ℤ)}) → IsArithFrobAt ℤ φ Q) ∧
      ∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - φ • x := by
  rcases h with h | h
  · refine ⟨σ, Or.inl rfl, ?_, h⟩
    intro Q _ hQ
    let : Q.LiesOver (Ideal.span {(p : ℤ)}) := hQ
    exact isArithFrobAt_of_integer_global_congruence p σ h Q
  · refine ⟨σ * τ, Or.inr rfl, ?_, h⟩
    intro Q _ hQ
    let : Q.LiesOver (Ideal.span {(p : ℤ)}) := hQ
    exact isArithFrobAt_of_integer_global_congruence p (σ * τ) h Q

end WeightedTorusJets


end SiegelZeros

end OAI
