import OAI.NumberTheory.Ostmann.Characters.CRTFourier
import OAI.NumberTheory.Ostmann.Characters.NormalizedCharacterPoisson

namespace OAI

/-! # Factoring the actual quadratic Gauss coefficient over coprime denominators -/

namespace Ostmann

open scoped Classical BigOperators

 theorem jacobiComplex_crt {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (x : ZMod (m * n)) :
    jacobiComplex (m * n) x =
      jacobiComplex m ((ZMod.chineseRemainder h) x).1 *
      jacobiComplex n ((ZMod.chineseRemainder h) x).2 := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  have he : (ZMod.chineseRemainder h) (z : ZMod (m * n)) =
      ((z : ZMod m), (z : ZMod n)) := map_intCast (ZMod.chineseRemainder h) z
  rw [he]
  change jacobiComplex (m * n) (z : ZMod (m * n)) =
    jacobiComplex m (z : ZMod m) * jacobiComplex n (z : ZMod n)
  rw [jacobiComplex_intCast, jacobiComplex_intCast, jacobiComplex_intCast,
    jacobiSym.mul_right' z (NeZero.ne m) (NeZero.ne n)]
  push_cast
  rfl

 theorem jacobiComplex_inv_unit (m : ℕ) [NeZero m] (x : ZMod m) (hx : IsUnit x) :
    jacobiComplex m x⁻¹ = jacobiComplex m x := by
  have hmul : jacobiComplex m x * jacobiComplex m x⁻¹ = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit x hx, map_one]
  have hsq : jacobiComplex m x * jacobiComplex m x = 1 := by
    have hh := congrArg (fun χ : DirichletCharacter ℂ m => χ x)
      (jacobiComplex_isQuadratic m).sq_eq_one
    simpa only [pow_two, MulChar.coeToFun_mul, Pi.mul_apply, MulChar.one_apply hx] using hh
  exact mul_left_cancel₀ (IsUnit.ne_zero (hx.map (jacobiComplex m))) (hmul.trans hsq.symm)

 theorem quadratic_gauss_crt {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (hm : Squarefree m) (hn : Squarefree n)
    (hom : Odd m) (hon : Odd n) :
    gaussSum (jacobiComplex (m * n)) ZMod.stdAddChar =
      jacobiComplex m (n : ZMod m) * jacobiComplex n (m : ZMod n) *
        gaussSum (jacobiComplex m) ZMod.stdAddChar *
        gaussSum (jacobiComplex n) ZMod.stdAddChar := by
  have hp := additiveFourier_crt h (jacobiComplex m) (jacobiComplex n) (-1)
  have heq : (fun x : ZMod (m * n) =>
      jacobiComplex m ((ZMod.chineseRemainder h) x).1 *
      jacobiComplex n ((ZMod.chineseRemainder h) x).2) = jacobiComplex (m * n) :=
    funext (fun x => (jacobiComplex_crt h x).symm)
  rw [heq, primitive_character_fourier _
      (jacobiComplex_squarefree_primitive (m * n) ((Nat.squarefree_mul h).mpr ⟨hm, hn⟩)
        (hom.mul hon)),
    primitive_character_fourier _ (jacobiComplex_squarefree_primitive m hm hom),
    primitive_character_fourier _ (jacobiComplex_squarefree_primitive n hn hon),
    (jacobiComplex_isQuadratic (m * n)).inv,
    (jacobiComplex_isQuadratic m).inv, (jacobiComplex_isQuadratic n).inv] at hp
  simp only [map_neg, map_one, Prod.fst_neg, Prod.snd_neg, Prod.fst_one, Prod.snd_one,
    mul_neg, mul_one, neg_neg] at hp
  rw [jacobiComplex_inv_unit m _ ((ZMod.isUnit_iff_coprime n m).mpr h.symm),
    jacobiComplex_inv_unit n _ ((ZMod.isUnit_iff_coprime m n).mpr h)] at hp
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  push_cast at hp
  field_simp [hm0, hn0] at hp
  linear_combination hp

 theorem quadratic_gauss_phase_crt {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (hm : Squarefree m) (hn : Squarefree n)
    (hom : Odd m) (hon : Odd n) :
    jacobiGaussPhase (m * n) =
      jacobiComplex m (n : ZMod m) * jacobiComplex n (m : ZMod n) *
        jacobiGaussPhase m * jacobiGaussPhase n := by
  unfold jacobiGaussPhase
  rw [quadratic_gauss_crt h hm hn hom hon, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg m), Complex.ofReal_mul]
  ring

end Ostmann

end OAI
