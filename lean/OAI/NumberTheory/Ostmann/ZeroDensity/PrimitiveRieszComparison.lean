import OAI.NumberTheory.Ostmann.ZeroDensity.RieszCoprimeComparison
import OAI.NumberTheory.Ostmann.Characters.PrimitiveCharacterReduction

namespace OAI

/-! # Riesz means after passage to the actual primitive character -/

namespace Ostmann

noncomputable def reducedRieszMean (e : Option PrimitiveComplexCharacter) (X : ℝ) : ℂ :=
  match e with
  | none => principalRieszMean X
  | some χ => characterRieszMean χ X

theorem primitiveReduction_divides {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ρ : PrimitiveComplexCharacter) (hρ : primitiveCharacterReduction χ = some ρ) : ρ.modulus ∣ q := by
  rw [primitiveCharacterReduction_modulus χ ρ hρ]
  exact χ.conductor_dvd_level

theorem primitiveReduction_agrees {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ρ : PrimitiveComplexCharacter) (hρ : primitiveCharacterReduction χ = some ρ)
    (n : ℕ) (hn : n.Coprime q) : χ (n : ZMod q) = ρ.character (n : ZMod ρ.modulus) := by
  have hd := primitiveReduction_divides χ ρ hρ
  have he := lift_primitiveCharacterReduction χ
  rw [hρ] at he
  simp only [liftPrimitiveCharacter, dite_eq_left hd] at he
  rw [← he]
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime n q).mpr hn
  rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu, ZMod.cast_natCast hd]

theorem rieszTwistMean_primitive_comparison {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (X : ℝ) (hX : 1 ≤ X) :
    ‖rieszTwistMean (fun n => χ (n : ZMod q)) X -
        reducedRieszMean (primitiveCharacterReduction χ) X‖ ≤
      2 * q * Real.log X + 4 * Real.sqrt X * Real.log X := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hXp : 0 < X := by linarith
  cases he : primitiveCharacterReduction χ with
  | none =>
    have hχ : χ = 1 := by
      have hh := lift_primitiveCharacterReduction χ
      rw [he] at hh
      exact hh.symm
    simp only [reducedRieszMean]
    rw [← rieszTwistMean_eq_principal X hXp]
    apply rieszTwistMean_coprime_comparison _ _ q X hq hX
      (fun n => χ.norm_le_one _) (by intro n; simp)
    intro n hn
    rw [hχ]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hn)
  | some ρ =>
    simp only [reducedRieszMean]
    rw [← rieszTwistMean_eq_character ρ X hXp]
    exact rieszTwistMean_coprime_comparison _ _ q X hq hX
      (fun n => χ.norm_le_one _) (fun n => ρ.character.norm_le_one _)
      (primitiveReduction_agrees χ ρ he)

end Ostmann

end OAI
