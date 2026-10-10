import OAI.NumberTheory.Ostmann.ZeroDensity.RealCharacterComplexification

namespace OAI

/-! # Quadratic complex characters as real primitive characters -/

namespace Ostmann

open Complex

theorem quadratic_character_im_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ ^ 2 = 1) (x : ZMod q) : (χ x).im = 0 := by
  by_cases hx : IsUnit x
  · have hh := congrArg (fun ψ : DirichletCharacter ℂ q => ψ x) hχ
    have hs : χ x ^ 2 = 1 := by simpa only [pow_two, MulChar.mul_apply, MulChar.one_apply hx] using hh
    rcases (sq_eq_one_iff).mp hs with he | he <;> simp [he]
  · rw [χ.map_nonunit hx]
    rfl

noncomputable def realPartCharacter {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : ∀ x, (χ x).im = 0) : DirichletCharacter ℝ q where
  toFun x := (χ x).re
  map_one' := by simp
  map_mul' := by
    intro x y
    simp only [map_mul, Complex.mul_re, hχ, mul_zero, sub_zero]
  map_nonunit' := by intro x hx; simp [χ.map_nonunit hx]

theorem realPartCharacter_complexification {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : ∀ x, (χ x).im = 0) :
    (realPartCharacter χ hχ).ringHomComp Complex.ofRealHom = χ := by
  ext x
  apply Complex.ext
  · rfl
  · simpa only [MulChar.ringHomComp_apply, Complex.ofRealHom_eq_coe, Complex.ofReal_im] using (hχ x).symm

theorem complexification_conductor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q) :
    DirichletCharacter.conductor (χ.ringHomComp Complex.ofRealHom) = χ.conductor := by
  have hf (d : ℕ) : DirichletCharacter.FactorsThrough
      (χ.ringHomComp Complex.ofRealHom) d ↔ χ.FactorsThrough d := by
    by_cases hd : d ∣ q
    · rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd,
        DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
      constructor <;> intro h x hx
      · have hh := h hx
        rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one] at hh ⊢
        simpa using hh
      · have hh := h hx
        rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one] at hh ⊢
        simp [hh]
    · exact ⟨fun h => (hd h.dvd).elim, fun h => (hd h.dvd).elim⟩
  unfold DirichletCharacter.conductor
  congr 1
  ext d
  exact hf d

noncomputable def PrimitiveComplexCharacter.asReal (χ : PrimitiveComplexCharacter)
    (hχ : χ.character ^ 2 = 1) : PrimitiveRealCharacter where
  modulus := χ.modulus
  positive := χ.positive
  character := realPartCharacter χ.character (quadratic_character_im_zero χ.character hχ)
  primitive := by
    let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
    rw [DirichletCharacter.isPrimitive_def, ← complexification_conductor,
      realPartCharacter_complexification]
    exact χ.primitive
  nontrivial := by
    intro he
    apply χ.nontrivial
    rw [← realPartCharacter_complexification χ.character (quadratic_character_im_zero χ.character hχ), he]
    simp

@[simp] theorem PrimitiveComplexCharacter.asReal_asComplex (χ : PrimitiveComplexCharacter)
    (hχ : χ.character ^ 2 = 1) : (χ.asReal hχ).asComplex = χ := by
  cases χ
  dsimp only [asReal, PrimitiveRealCharacter.asComplex, PrimitiveRealCharacter.complexCharacter]
  congr
  exact realPartCharacter_complexification _ _

end Ostmann

end OAI
