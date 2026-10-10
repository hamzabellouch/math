import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Characters.IntegerCharacter
import OAI.NumberTheory.SiegelZeros.Determinants.SqrtPairFrobeniusDirections

namespace OAI

namespace SiegelZeros

open scoped NumberField
namespace WeightedTorusJets

theorem source_frobenius_of_retained_character_field
    (q : ℕ) (L : Type*) [Field L] [NumberField L]
    [NeZero (8 * q)] [IsCyclotomicExtension {8 * q} ℚ L] [IsAbelianGalois ℚ L]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (a b : L)
    (hchar : IntermediateField.adjoin ℚ {a} = characterField (8 * q) L ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ)) :
    let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
    let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    ∀ (_ : Module.finrank ℚ B = 4)
      (σ τ : B ≃ₐ[ℚ] B) (_ : τ a' = a')
      (_ : Nat.card (B ≃ₐ[ℚ] B) = 4)
      (_ : ∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ),
      ∀ p : ℕ, p.Prime → ¬ p ∣ 2 * q → χ p = -1 →
        ((∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - σ • x) ∨
          (∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - (σ * τ) • x)) := by
  dsimp
  let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  intro hdegree σ τ hτa hcard hall p hp hpn hχp
  let : IsGalois ℚ B := IsGalois.of_card_aut_eq_finrank ℚ B (hcard.trans hdegree.symm)
  have hquad := real_character_isQuadratic χ hreal
  have hquad' : (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ).IsQuadratic := by
    rw [MulChar.isQuadratic_iff_sq_eq_one, ← map_pow, hquad.sq_eq_one, map_one]
  have hc : p.Coprime (2 * q) := hp.coprime_iff_not_dvd.mpr hpn
  have hpm : p.Coprime (8 * q) := by
    simpa only [show 8 = 2 ^ 3 from rfl, Nat.coprime_mul_iff_right,
      Nat.coprime_pow_right_iff (by decide : 0 < (3 : ℕ))] using hc
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ, hfrob, hglobal⟩ := exists_cyclotomic_frobenius_congruence (8 * q) L p
    (hp.coprime_iff_not_dvd.mp hpm)
  obtain ⟨P, hP, hover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 L) (Ideal.span {(p : ℤ)})
  have hφa : φ a ≠ a := by
    intro hfix
    have hmem := (mem_adjoin_fixingSubgroup_iff a φ).mpr hfix
    rw [hchar] at hmem
    have hval := (mem_characterField_fixingSubgroup (8 * q) L ℂ _ hquad' φ).mp hmem
    rw [galEquivZMod_arithFrob (8 * q) L hp hpm P hover.over.symm φ
      (hfrob P inferInstance hover)] at hval
    have hcast : (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ)
        (ZMod.unitOfCoprime p hpm) = χ p := by
      rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
      simp
    rw [hcast, hχp] at hval
    norm_num at hval
  let ψ := φ.restrictNormal B
  have hψa : ψ a' ≠ a' := by
    intro h
    apply hφa
    simpa [ψ, a', AlgEquiv.restrictNormal_apply] using congrArg (fun x : B => (x : L)) h
  have hψglobal : ∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - ψ • x :=
    frobenius_congruence_descends B.val ψ φ (fun x => AlgEquiv.restrictNormal_apply B φ x) p hglobal
  rcases hall ψ with hψ | hψ | hψ | hψ
  · exact (hψa (hψ ▸ AlgEquiv.one_apply a')).elim
  · exact Or.inl (hψ ▸ hψglobal)
  · exact (hψa (hψ ▸ hτa)).elim
  · exact Or.inr (hψ ▸ hψglobal)

end WeightedTorusJets


end SiegelZeros

end OAI
