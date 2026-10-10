import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Characters.QuadraticGroupCharacterFrobenius

namespace OAI

namespace SiegelZeros

open scoped NumberField
namespace WeightedTorusJets

theorem quadraticEigencharacter_autCongr {K L : Type*}
    [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    (e : K ≃ₐ[ℚ] L) (a : K) (b : L) (d : ℚ)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ L d)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (he : e a = b) (f : K ≃ₐ[ℚ] K) :
    quadraticEigencharacter b d hb hb0 (AlgEquiv.autCongr e f) =
      e (quadraticEigencharacter a d ha ha0 f) := by
  simp [quadraticEigencharacter, ← he, AlgEquiv.autCongr_apply]

theorem quadraticEigencharacter_autCongr_complex {K L : Type*}
    [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    (e : K ≃ₐ[ℚ] L) (a : K) (b : L) (d : ℚ)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ L d)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (he : e a = b)
    (ν : L →ₐ[ℚ] ℂ) (f : K ≃ₐ[ℚ] K) :
    ν (quadraticEigencharacter b d hb hb0 (AlgEquiv.autCongr e f)) =
      (ν.comp e.toAlgHom) (quadraticEigencharacter a d ha ha0 f) :=
  congrArg ν (quadraticEigencharacter_autCongr e a b d ha hb ha0 hb0 he f)

theorem source_quadratic_group_character_principal_transport
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    (e : K ≃ₐ[ℚ] L) (a : K) (b : L) (d : ℚ)
    (ha : a ^ 2 = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ L d)
    (hd : ¬ IsSquare d) (he : e a = b)
    (σ τ : K ≃ₐ[ℚ] K) (hσ : σ a = -a) (hτ : τ a = a)
    (ν : L →ₐ[ℚ] ℂ) (q : ℕ) (χ : DirichletCharacter ℂ q)
    (hfrob : ∀ p : ℕ, p.Prime → ¬ p ∣ 2 * q → χ p = -1 →
      ((∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - σ • x) ∨
        (∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - (σ * τ) • x))) :
    ∃ hb0 : b ≠ 0,
      let ξ := quadraticEigencharacter b d hb hb0
      (∀ f, f b = ξ f * b) ∧
      (∀ f, ξ f = 1 ∨ ξ f = -1) ∧
      ξ (AlgEquiv.autCongr e σ) = -1 ∧ ξ (AlgEquiv.autCongr e τ) = 1 ∧
      ξ (AlgEquiv.autCongr e σ * AlgEquiv.autCongr e τ) = -1 ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ 2 * q → χ p = -1 →
        ∃ φ : K ≃ₐ[ℚ] K, (φ = σ ∨ φ = σ * τ) ∧
          (∀ (P : Ideal (𝓞 L)) (_ : P.IsPrime),
            P.LiesOver (Ideal.span {(p : ℤ)}) → IsArithFrobAt ℤ (AlgEquiv.autCongr e φ) P) ∧
          ν (ξ (AlgEquiv.autCongr e φ)) = χ p ∧
          ∀ x : 𝓞 L, (p : 𝓞 L) ∣ x ^ p - AlgEquiv.autCongr e φ • x := by
  have ha0 : a ≠ 0 := by
    intro h
    have hd0 : d = 0 := (algebraMap ℚ K).injective (by simpa [h] using ha.symm)
    exact hd (hd0 ▸ IsSquare.zero)
  have hb0 : b ≠ 0 := he ▸ (map_ne_zero e).mpr ha0
  have ha' : a * a = algebraMap ℚ K d := by simpa [pow_two] using ha
  obtain ⟨ξK, hξK, hrange, hξσ, hξτ, hξστ, hprimes⟩ :=
    source_quadratic_group_character_with_frobenius a d ha hd σ τ hσ hτ
      (ν.comp e.toAlgHom) q χ hfrob
  let ξ := quadraticEigencharacter b d hb hb0
  have hnat (f : K ≃ₐ[ℚ] K) : ξ (AlgEquiv.autCongr e f) = e (ξK f) :=
    (quadraticEigencharacter_autCongr e a b d ha' hb ha0 hb0 he f).trans
      (congrArg e (div_eq_of_eq_mul ha0 (hξK f)))
  refine ⟨hb0, fun f => (quadraticEigencharacter_apply_mul b d hb hb0 f).symm,
    quadraticEigencharacter_range b d hb hb0, ?_, ?_, ?_, ?_⟩
  · simpa [hξσ] using hnat σ
  · simpa [hξτ] using hnat τ
  · simpa only [map_mul, hξστ, map_neg, map_one] using hnat (σ * τ)
  · intro p hp hpn hχp
    obtain ⟨φ, hchoice, _, hvalue, hglobal⟩ := hprimes p hp hpn hχp
    have hglobal' := integer_frobenius_transport e φ p hglobal
    refine ⟨φ, hchoice, ?_, ?_, hglobal'⟩
    · intro P _ hP
      let : P.LiesOver (Ideal.span {(p : ℤ)}) := hP
      exact isArithFrobAt_of_integer_global_congruence p (AlgEquiv.autCongr e φ) hglobal' P
    · exact (congrArg ν (hnat φ)).trans hvalue

end WeightedTorusJets


end SiegelZeros

end OAI
