import OAI.NumberTheory.Ostmann.ZeroDensity.RealCharacterReflection

namespace OAI

/-! # Distinct primitive characters remain distinct at a common level -/

namespace Ostmann

theorem PrimitiveComplexCharacter.eq_of_changeLevel_eq (χ ψ : PrimitiveComplexCharacter)
    {N : ℕ} [NeZero N] (hχ : χ.modulus ∣ N) (hψ : ψ.modulus ∣ N)
    (he : DirichletCharacter.changeLevel hχ χ.character =
      DirichletCharacter.changeLevel hψ ψ.character) : χ = ψ := by
  have hm : χ.modulus = ψ.modulus := by
    have hh := congrArg DirichletCharacter.conductor he
    rw [DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel] at hh
    exact χ.primitive.symm.trans (hh.trans ψ.primitive)
  cases χ with
  | mk q hq χ hprim hn =>
    cases ψ with
    | mk r hr ψ hprim' hn' =>
      dsimp only at hm hχ hψ he
      subst r
      have hc : χ = ψ := DirichletCharacter.changeLevel_injective hχ he
      subst ψ
      rfl

theorem PrimitiveRealCharacter.asComplex_injective :
    Function.Injective PrimitiveRealCharacter.asComplex := by
  intro χ ψ he
  have hm : χ.modulus = ψ.modulus := congrArg PrimitiveComplexCharacter.modulus he
  cases χ with
  | mk q hq χ hprim hn =>
    cases ψ with
    | mk r hr ψ hprim' hn' =>
      dsimp only at hm
      subst r
      have hc : χ = ψ := by
        let : NeZero q := ⟨hq.ne'⟩
        have hh := congrArg (fun η : PrimitiveComplexCharacter => fun n : ℕ => η.character n) he
        apply MulChar.ext
        intro x
        apply Complex.ofReal_injective
        have hv := congrFun hh (x : ZMod q).val
        change (χ (((x : ZMod q).val : ℕ) : ZMod q) : ℂ) =
          (ψ (((x : ZMod q).val : ℕ) : ZMod q) : ℂ) at hv
        simpa only [ZMod.natCast_zmod_val] using hv
      subst ψ
      rfl

theorem PrimitiveRealCharacter.lift_inverse_eq (χ : PrimitiveRealCharacter)
    {N : ℕ} (hχ : χ.modulus ∣ N) :
    (DirichletCharacter.changeLevel hχ χ.complexCharacter)⁻¹ =
      DirichletCharacter.changeLevel hχ χ.complexCharacter := by
  rw [← map_inv, χ.complex_inv_eq]

theorem distinct_real_lifts_product_nonprincipal (χ ψ : PrimitiveRealCharacter)
    (hne : χ ≠ ψ) {N : ℕ} [NeZero N] (hχ : χ.modulus ∣ N) (hψ : ψ.modulus ∣ N) :
    DirichletCharacter.changeLevel hχ χ.complexCharacter *
      DirichletCharacter.changeLevel hψ ψ.complexCharacter ≠ 1 := by
  intro he
  have heq := (eq_inv_iff_mul_eq_one.mpr he).trans (ψ.lift_inverse_eq hψ)
  have hc := χ.asComplex.eq_of_changeLevel_eq ψ.asComplex hχ hψ heq
  exact hne (PrimitiveRealCharacter.asComplex_injective hc)

end Ostmann

end OAI
