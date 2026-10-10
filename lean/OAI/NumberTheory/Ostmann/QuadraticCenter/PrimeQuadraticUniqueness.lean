import OAI.NumberTheory.Ostmann.Characters.CharacterHigherBias
import OAI.NumberTheory.Ostmann.QuadraticSieve.PrimeJacobiCharacter

namespace OAI

/-! # The only nonprincipal quadratic character at a prime -/
namespace Ostmann

noncomputable def complexJacobiCharacter (p : ℕ) [NeZero p] : DirichletCharacter ℂ p :=
  (jacobiCharacterInt p).ringHomComp (Int.castRingHom ℂ)

theorem prime_character_eq_of_square_eq_one {p : ℕ} [Fact p.Prime]
    (χ ψ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hχ2 : χ ^ 2 = 1) (hψ2 : ψ ^ 2 = 1) : χ = ψ := by
  obtain ⟨g, hg⟩ := exists_zpow_surjective (ZMod p)ˣ
  have hext (φ θ : DirichletCharacter ℂ p) (heq : φ g = θ g) : φ = θ := by
    apply MulChar.equivToUnitHom.injective
    apply MonoidHom.ext
    intro u
    obtain ⟨z, rfl⟩ := hg u
    change φ.toUnitHom (g ^ z) = θ.toUnitHom (g ^ z)
    rw [map_zpow, map_zpow]
    congr 1
    exact Units.ext heq
  have hneg (φ : DirichletCharacter ℂ p) (hφ : φ ≠ 1) (hφ2 : φ ^ 2 = 1) : φ g = -1 := by
    have hs : φ g ^ 2 = 1 := by
      have hh := congrArg (fun θ : DirichletCharacter ℂ p => θ g) hφ2
      simpa only [MulChar.pow_apply_coe, MulChar.one_apply g.isUnit] using hh
    rcases sq_eq_one_iff.mp hs with hh | hh
    · exact (hφ (hext φ 1 (by simpa only [MulChar.one_apply g.isUnit] using hh))).elim
    · exact hh
  exact hext χ ψ ((hneg χ hχ hχ2).trans (hneg ψ hψ hψ2).symm)

theorem complexJacobiCharacter_square {p : ℕ} [Fact p.Prime] :
    complexJacobiCharacter p ^ 2 = 1 := by
  apply MulChar.IsQuadratic.sq_eq_one
  change ((jacobiCharacterInt p).ringHomComp (Int.castRingHom ℂ)).IsQuadratic
  rw [jacobiCharacterInt_prime]
  exact (quadraticChar_isQuadratic (ZMod p)).comp _

theorem complexJacobiCharacter_ne_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    complexJacobiCharacter p ≠ 1 := by
  have hc : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp2
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hc
  intro he
  have hev := congrArg (fun χ : DirichletCharacter ℂ p => χ a) he
  have hneg : complexJacobiCharacter p a = -1 := by
    simp only [complexJacobiCharacter, MulChar.ringHomComp_apply, jacobiCharacterInt_prime]
    rw [ha]
    norm_num
  rw [hneg, MulChar.one_apply a.isUnit] at hev
  norm_num at hev

theorem prime_quadratic_character_unique {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (hχ2 : χ ^ 2 = 1) :
    χ = complexJacobiCharacter p :=
  prime_character_eq_of_square_eq_one χ _ hχ (complexJacobiCharacter_ne_one hp2)
    hχ2 complexJacobiCharacter_square

end Ostmann

end OAI
