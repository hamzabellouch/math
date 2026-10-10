import Mathlib.Analysis.Fourier.ZMod
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import OAI.NumberTheory.SiegelZeros.Structure.GaussLegendre

namespace OAI

namespace SiegelZeros


namespace SiegelZerosAwei.W09

open scoped ComplexConjugate

variable {q : ℕ} [NeZero q]

def IsRealCharacter (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ a, (χ a).im = 0

omit [NeZero q] in
theorem realCharacter_isQuadratic (χ : DirichletCharacter ℂ q)
    (hχ : IsRealCharacter χ) : χ.IsQuadratic := by
  have hs : star χ = χ := by
    ext a
    exact Complex.conj_eq_iff_im.mpr (hχ a)
  have hi : χ⁻¹ = χ := (MulChar.star_eq_inv χ).symm.trans hs
  apply MulChar.isQuadratic_iff_sq_eq_one.mpr
  calc
    χ ^ 2 = χ * χ := pow_two χ
    _ = χ⁻¹ * χ := congrArg (fun ψ ↦ ψ * χ) hi.symm
    _ = 1 := inv_mul_cancel χ

omit [NeZero q] in
theorem isQuadratic_isRealCharacter (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) : IsRealCharacter χ := by
  intro a
  rcases hχ a with h | h | h <;> simp [h]

omit [NeZero q] in
theorem realCharacter_orderOf (χ : DirichletCharacter ℂ q)
    (hr : IsRealCharacter χ) (hn : χ ≠ 1) : orderOf χ = 2 := by
  exact orderOf_eq_prime (realCharacter_isQuadratic χ hr).sq_eq_one hn

noncomputable def characterGaussSum (χ : DirichletCharacter ℂ q) : ℂ :=
  gaussSum χ ZMod.stdAddChar

theorem characterGaussSum_sq (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    characterGaussSum χ ^ 2 = χ (-1) * (q : ℂ) := by
  have hf (k : ZMod q) :
      ZMod.dft (χ : ZMod q → ℂ) k = χ (-k) * characterGaussSum χ := by
    simpa only [hq.inv, characterGaussSum] using
      hp.fourierTransform_eq_inv_mul_gaussSum k
  have he : ZMod.dft (χ : ZMod q → ℂ) =
      fun k ↦ χ (-k) * characterGaussSum χ := funext hf
  have hdouble := congr_fun (ZMod.dft_dft (χ : ZMod q → ℂ)) (1 : ZMod q)
  rw [he, ZMod.dft_mul_const, ZMod.dft_comp_neg] at hdouble
  simp only [hf, neg_neg, map_one, one_mul, smul_eq_mul] at hdouble
  simpa only [pow_two, mul_comm] using hdouble

noncomputable def characterField (χ : DirichletCharacter ℂ q) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {characterGaussSum χ}

theorem characterGaussSum_mem_field (χ : DirichletCharacter ℂ q) :
    characterGaussSum χ ∈ characterField χ := by
  exact IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)

theorem characterGaussSum_ne_zero (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hq : χ.IsQuadratic) : characterGaussSum χ ≠ 0 := by
  intro hz
  have hs := characterGaussSum_sq χ hp hq
  rw [hz, zero_pow (by decide : 2 ≠ 0)] at hs
  have hu : χ (-1) ≠ 0 := (isUnit_neg_one.map χ).ne_zero
  exact mul_ne_zero hu (NeZero.ne (q : ℂ)) hs.symm

theorem characterGaussSum_isIntegral (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    IsIntegral ℤ (characterGaussSum χ) := by
  apply IsIntegral.of_pow (n := 2) (by decide)
  rw [characterGaussSum_sq χ hp hq]
  rcases hq (-1) with h | h | h
  · simp only [h, zero_mul]
    exact isIntegral_zero
  · simp only [h, one_mul]
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (q : ℤ)))
  · simp only [h, neg_one_mul]
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := -(q : ℤ)))

end SiegelZerosAwei.W09



namespace SiegelZerosAwei.W09

variable {q : ℕ}

noncomputable def integerCharacterValue (χ : DirichletCharacter ℂ q) (a : ZMod q) : ℤ :=
  if χ a = 0 then 0 else if χ a = 1 then 1 else -1

theorem integerCharacterValue_cast (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) (a : ZMod q) :
    (integerCharacterValue χ a : ℂ) = χ a := by
  rcases hq a with h | h | h <;> simp [integerCharacterValue, h]
  intro he
  exact he.symm

noncomputable def integerCharacter (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) : DirichletCharacter ℤ q where
  toFun := integerCharacterValue χ
  map_one' := by
    apply Int.cast_injective (α := ℂ)
    simpa only [integerCharacterValue_cast χ hq, Int.cast_one] using χ.map_one
  map_mul' a b := by
    apply Int.cast_injective (α := ℂ)
    simpa only [integerCharacterValue_cast χ hq, Int.cast_mul] using map_mul χ a b
  map_nonunit' a ha := by
    simp [integerCharacterValue, χ.map_nonunit ha]

@[simp] theorem integerCharacter_cast (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) (a : ZMod q) : (integerCharacter χ hq a : ℂ) = χ a :=
  integerCharacterValue_cast χ hq a

theorem integerCharacter_isQuadratic (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) : (integerCharacter χ hq).IsQuadratic := by
  intro a
  change integerCharacterValue χ a = 0 ∨ integerCharacterValue χ a = 1 ∨
    integerCharacterValue χ a = -1
  unfold integerCharacterValue
  split_ifs <;> simp

theorem integerCharacter_complexification (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) :
    (integerCharacter χ hq).ringHomComp (Int.castRingHom ℂ) = χ := by
  ext a
  exact integerCharacter_cast χ hq a

noncomputable def reducedIntegerCharacter (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) (R : Type*) [CommRing R] : DirichletCharacter R q :=
  (integerCharacter χ hq).ringHomComp (Int.castRingHom R)

theorem reducedIntegerCharacter_isQuadratic (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) (R : Type*) [CommRing R] :
    (reducedIntegerCharacter χ hq R).IsQuadratic :=
  (integerCharacter_isQuadratic χ hq).comp (Int.castRingHom R)

theorem reducedGaussSum_frobenius [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : χ.IsQuadratic)
    (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (hpq : p.Coprime q) (ψ : AddChar (ZMod q) R) :
    gaussSum (reducedIntegerCharacter χ hq R) ψ ^ p =
      (integerCharacter χ hq (p : ZMod q) : R) *
        gaussSum (reducedIntegerCharacter χ hq R) ψ := by
  exact (reducedIntegerCharacter_isQuadratic χ hq R).gaussSum_frob p
    ((ZMod.isUnit_iff_coprime p q).mpr hpq) ψ

end SiegelZerosAwei.W09



namespace Awei.W39
open SiegelZerosAwei.W09

theorem character_legendre_of_reduced_gaussSum_sq
    {q : ℕ} [NeZero q] {F : Type*} [Field F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (hp : p ≠ 2)
    (χ : DirichletCharacter ℂ q) (hq : χ.IsQuadratic)
    (hu : IsUnit (p : ZMod q)) (ψ : AddChar (ZMod q) F) (D : ℤ)
    (hD : (D : F) ≠ 0)
    (hs : gaussSum (reducedIntegerCharacter χ hq F) ψ ^ 2 = (D : F)) :
    χ (p : ZMod q) = (legendreSym p D : ℂ) := by
  have he := integerCharacter_legendre_of_gaussSum_sq p hp
    (integerCharacter χ hq) (integerCharacter_isQuadratic χ hq) hu ψ D hD hs
  have hc := congrArg (Int.cast : ℤ → ℂ) he
  simpa only [integerCharacter_cast] using hc

theorem character_legendre_of_signed_gaussSum_sq
    {q : ℕ} [NeZero q] {F : Type*} [Field F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (hp : p ≠ 2) (hpq : ¬ p ∣ q)
    (χ : DirichletCharacter ℂ q) (hq : χ.IsQuadratic)
    (ψ : AddChar (ZMod q) F) (D : ℤ) (hDabs : D.natAbs = q)
    (hs : gaussSum (reducedIntegerCharacter χ hq F) ψ ^ 2 = (D : F)) :
    χ (p : ZMod q) = (legendreSym p D : ℂ) := by
  have hu : IsUnit (p : ZMod q) :=
    (ZMod.isUnit_iff_coprime p q).mpr
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpq)
  have hD : (D : F) ≠ 0 := intCast_ne_zero_of_not_dvd_natAbs p D (by rwa [hDabs])
  exact character_legendre_of_reduced_gaussSum_sq p hp χ hq hu ψ D hD hs

end Awei.W39


end SiegelZeros

end OAI
