import OAI.NumberTheory.Ostmann.Characters.PrimitiveLiftReduction
import OAI.NumberTheory.Ostmann.ZeroDensity.InducedCharacterRieszDecay

namespace OAI

/-! # The exact principal and exceptional terms after character summation -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem reducedRieszMain_no_exception (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (X : ℝ) (he : actualLocalZero q = none) :
    reducedRieszMain q (primitiveCharacterReduction χ) X =
      if χ = 1 then ((X / 2 : ℝ) : ℂ) else 0 := by
  classical
  cases hr : primitiveCharacterReduction χ with
  | none =>
    have hχ := (primitiveCharacterReduction_eq_none_iff q χ).mp hr
    simp only [reducedRieszMain, hχ, ↓reduceIte]
  | some ρ =>
    have hχ : χ ≠ 1 := by
      intro h
      have hn := (primitiveCharacterReduction_eq_none_iff q χ).mpr h
      rw [hr] at hn
      cases hn
    simp only [reducedRieszMain, canonicalCharacterRieszTerm, he, hχ, ↓reduceIte]

theorem reducedRieszMain_exception (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (X : ℝ) (e : PrimitiveRealZero) (he : actualLocalZero q = some e) :
    let hd := (actualLocalZero_spec q e he).1
    let τ := DirichletCharacter.changeLevel hd e.asRealCharacter.asComplex.character
    reducedRieszMain q (primitiveCharacterReduction χ) X =
      (if χ = 1 then ((X / 2 : ℝ) : ℂ) else 0) -
        (if χ = τ then rieszContourWeight X (e.beta : ℂ) else 0) := by
  classical
  dsimp only
  let R := e.asRealCharacter.asComplex
  let hd := (actualLocalZero_spec q e he).1
  let τ := DirichletCharacter.changeLevel hd R.character
  have hτ : τ ≠ 1 := mt (DirichletCharacter.changeLevel_eq_one_iff hd).mp R.nontrivial
  change reducedRieszMain q (primitiveCharacterReduction χ) X =
    (if χ = 1 then ((X / 2 : ℝ) : ℂ) else 0) -
      (if χ = τ then rieszContourWeight X (e.beta : ℂ) else 0)
  cases hr : primitiveCharacterReduction χ with
  | none =>
    have hχ := (primitiveCharacterReduction_eq_none_iff q χ).mp hr
    simp only [reducedRieszMain, hχ, ↓reduceIte, Ne.symm hτ, sub_zero]
  | some ρ =>
    have hχ : χ ≠ 1 := by
      intro h
      have hn := (primitiveCharacterReduction_eq_none_iff q χ).mpr h
      rw [hr] at hn
      cases hn
    by_cases hρ : ρ = R
    · have hχτ : χ = τ := by
        apply (primitiveCharacterReduction_eq_some_iff q χ R hd).mp
        simpa only [hρ] using hr
      simp only [reducedRieszMain, canonicalCharacterRieszTerm, he, hρ, R, hχτ, hτ,
        ↓reduceIte, zero_sub]
    · have hχτ : χ ≠ τ := by
        intro h
        have hh := primitiveCharacterReduction_lift q R hd
        change primitiveCharacterReduction τ = some R at hh
        rw [← h, hr] at hh
        exact hρ (Option.some.inj hh)
      simp only [reducedRieszMain, canonicalCharacterRieszTerm, he,
        show e.asRealCharacter.asComplex ≠ ρ from Ne.symm hρ, hχ, hχτ, ↓reduceIte, sub_zero]

theorem principal_character_inverse_value (q : ℕ) (a : ZMod q) (ha : IsUnit a) :
    (1 : DirichletCharacter ℂ q) a⁻¹ = 1 := by
  obtain ⟨u, rfl⟩ := ha
  rw [ZMod.inv_coe_unit]
  exact MulChar.one_apply_coe _

theorem rieszCharacterMainSum_no_exception (q : ℕ) [NeZero q] (a : ZMod q)
    (ha : IsUnit a) (X : ℝ) (he : actualLocalZero q = none) :
    (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * reducedRieszMain q (primitiveCharacterReduction χ) X) =
      (X / 2 : ℝ) := by
  classical
  simp_rw [reducedRieszMain_no_exception q _ X he]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    principal_character_inverse_value q a ha, one_mul]

theorem rieszCharacterMainSum_exception (q : ℕ) [NeZero q] (a : ZMod q)
    (ha : IsUnit a) (X : ℝ) (e : PrimitiveRealZero) (he : actualLocalZero q = some e) :
    let hd := (actualLocalZero_spec q e he).1
    let τ := DirichletCharacter.changeLevel hd e.asRealCharacter.asComplex.character
    (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * reducedRieszMain q (primitiveCharacterReduction χ) X) =
      (X / 2 : ℝ) - τ a⁻¹ * rieszContourWeight X (e.beta : ℂ) := by
  classical
  dsimp only
  simp_rw [reducedRieszMain_exception q _ X e he]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, principal_character_inverse_value q a ha, one_mul]

end Ostmann

end OAI
