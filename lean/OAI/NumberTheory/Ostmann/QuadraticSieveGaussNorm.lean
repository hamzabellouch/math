import OAI.NumberTheory.Ostmann.QuadraticSieveGauss

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped FourierTransform

theorem quadratic_gauss_sq {q : ℕ} [NeZero q] (hq : Odd q) (hsq : Squarefree q) :
    gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar ^ 2 =
      (q : ℂ) * (jacobiSym (-1) q : ℂ) := by
  let χ := jacobiDirichletCharacter q
  let τ := gaussSum χ ZMod.stdAddChar
  have hdft : ZMod.dft χ = (fun k : ZMod q => τ * χ (-k)) := by
    ext k
    rw [(jacobiDirichletCharacter_isPrimitive hq hsq).fourierTransform_eq_inv_mul_gaussSum,
      jacobiDirichletCharacter_inv]
    exact mul_comm _ _
  have hdouble := congrFun (ZMod.dft_dft (χ : ZMod q → ℂ)) (1 : ZMod q)
  rw [hdft, ZMod.dft_const_mul, ZMod.dft_comp_neg] at hdouble
  change τ * ZMod.dft χ (-1) = (q : ℂ) * χ (-1) at hdouble
  rw [hdft] at hdouble
  simp only [neg_neg, map_one, mul_one] at hdouble
  have hneg : χ (-1) = (jacobiSym (-1) q : ℂ) := by
    simpa only [Int.cast_neg, Int.cast_one] using jacobiDirichletCharacter_intCast q (-1)
  simpa only [pow_two, hneg] using hdouble

theorem quadratic_gauss_norm_sq {q : ℕ} [NeZero q] (hq : Odd q) (hsq : Squarefree q) :
    ‖gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar‖ ^ 2 = (q : ℝ) := by
  have hnorm : ‖(jacobiSym (-1) q : ℂ)‖ = 1 := by
    rcases jacobiSym.eq_one_or_neg_one (a := (-1 : ℤ)) (b := q) (by simp) with h | h <;> simp [h]
  have h := congrArg norm (quadratic_gauss_sq hq hsq)
  simpa only [norm_pow, norm_mul, Complex.norm_natCast, hnorm, mul_one] using h

end Ostmann.QuadraticSieve

end OAI
