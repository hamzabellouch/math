import OAI.NumberTheory.Ostmann.QuadraticSieveJacobiCharacter

namespace OAI

namespace Ostmann.QuadraticSieve

theorem fourier_div_eq_stdAddChar_mul (q : ℕ) [NeZero q] (h a : ℤ) :
    fourier h (((a : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) =
      ZMod.stdAddChar ((h : ZMod q) * (a : ZMod q)) := by
  rw [← Int.cast_mul, ZMod.stdAddChar_coe, fourier_coe_apply]
  push_cast
  congr 1
  ring

theorem sum_fin_residues_eq_sum_zmod (q : ℕ) [NeZero q] (f : ZMod q → ℂ) :
    (∑ a : Fin q, f (a.val : ZMod q)) = ∑ a : ZMod q, f a := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    apply Finset.sum_congr rfl
    intro a ha
    congr 1
    exact ZMod.natCast_zmod_val (n := q + 1) a

theorem jacobi_gauss_mulShift {q : ℕ} [NeZero q]
    (hq : Odd q) (hsq : Squarefree q) (h : ℤ) :
    gaussSum (jacobiDirichletCharacter q) (ZMod.stdAddChar.mulShift (h : ZMod q)) =
      (jacobiSym h q : ℂ) * gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar := by
  rw [gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar
      (jacobiDirichletCharacter_isPrimitive hq hsq),
    jacobiDirichletCharacter_inv, jacobiDirichletCharacter_intCast]

theorem finite_jacobi_gauss_transform {q : ℕ} [NeZero q]
    (hq : Odd q) (hsq : Squarefree q) (h : ℤ) :
    (∑ a : Fin q, (jacobiSym (a.val : ℤ) q : ℂ) *
      fourier h (((a.val : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)) =
      (jacobiSym h q : ℂ) * gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar := by
  calc
    (∑ a : Fin q, (jacobiSym (a.val : ℤ) q : ℂ) *
        fourier h (((a.val : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)) =
        ∑ a : Fin q, jacobiDirichletCharacter q (a.val : ZMod q) *
          ZMod.stdAddChar ((h : ZMod q) * (a.val : ZMod q)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [jacobiDirichletCharacter_natCast]
      congr 1
      simpa only [Int.cast_natCast] using fourier_div_eq_stdAddChar_mul q h (a.val : ℤ)
    _ = ∑ a : ZMod q, jacobiDirichletCharacter q a *
        ZMod.stdAddChar ((h : ZMod q) * a) :=
      sum_fin_residues_eq_sum_zmod q (fun a => jacobiDirichletCharacter q a *
        ZMod.stdAddChar ((h : ZMod q) * a))
    _ = gaussSum (jacobiDirichletCharacter q)
        (ZMod.stdAddChar.mulShift (h : ZMod q)) := rfl
    _ = _ := jacobi_gauss_mulShift hq hsq h

theorem jacobi_dft {q : ℕ} [NeZero q]
    (hq : Odd q) (hsq : Squarefree q) (h : ℤ) :
    ZMod.dft (jacobiDirichletCharacter q) (h : ZMod q) =
      (jacobiSym (-h) q : ℂ) * gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar := by
  rw [(jacobiDirichletCharacter_isPrimitive hq hsq).fourierTransform_eq_inv_mul_gaussSum,
    jacobiDirichletCharacter_inv, ← Int.cast_neg, jacobiDirichletCharacter_intCast]

end Ostmann.QuadraticSieve

end OAI
