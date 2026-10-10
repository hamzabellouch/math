import OAI.NumberTheory.Ostmann.QuadraticSieveHeathBrownPoisson

namespace OAI

namespace Ostmann.QuadraticCenter
open Ostmann.QuadraticSieve
open scoped BigOperators SchwartzMap FourierTransform

theorem translated_jacobi_gauss_sum {q : ℕ} [NeZero q]
    (hq : Odd q) (hsq : Squarefree q) (h t : ℤ) :
    (∑ a : ZMod q, jacobiDirichletCharacter q (a - (t : ZMod q)) *
      ZMod.stdAddChar ((h : ZMod q) * a)) =
    ZMod.stdAddChar ((h : ZMod q) * (t : ZMod q)) * (jacobiSym h q : ℂ) *
      gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar := by
  calc
    _ = ∑ a : ZMod q, jacobiDirichletCharacter q a *
        ZMod.stdAddChar ((h : ZMod q) * (a + (t : ZMod q))) := by
      symm
      exact Fintype.sum_equiv (Equiv.addRight (t : ZMod q)) _ _
        (fun a => by simp)
    _ = ZMod.stdAddChar ((h : ZMod q) * (t : ZMod q)) *
        gaussSum (jacobiDirichletCharacter q)
          (ZMod.stdAddChar.mulShift (h : ZMod q)) := by
      change _ = ZMod.stdAddChar ((h : ZMod q) * (t : ZMod q)) *
        ∑ a : ZMod q, jacobiDirichletCharacter q a * ZMod.stdAddChar ((h : ZMod q) * a)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [mul_add, AddChar.map_add_eq_mul]
      ring
    _ = _ := by rw [jacobi_gauss_mulShift hq hsq]; ring

theorem finite_translated_jacobi_gauss_transform {q : ℕ} [NeZero q]
    (hq : Odd q) (hsq : Squarefree q) (h t : ℤ) :
    (∑ a : Fin q, (jacobiSym ((a.val : ℤ) - t) q : ℂ) *
      fourier h (((a.val : ℝ) / q : ℝ) : UnitAddCircle)) =
    ZMod.stdAddChar ((h : ZMod q) * (t : ZMod q)) * (jacobiSym h q : ℂ) *
      gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar := by
  calc
    _ = ∑ a : Fin q, jacobiDirichletCharacter q ((a.val : ZMod q) - (t : ZMod q)) *
        ZMod.stdAddChar ((h : ZMod q) * (a.val : ZMod q)) := by
      apply Finset.sum_congr rfl
      intro a ha
      have hc : jacobiDirichletCharacter q ((a.val : ZMod q) - (t : ZMod q)) =
          (jacobiSym ((a.val : ℤ) - t) q : ℂ) := by
        simpa only [Int.cast_sub, Int.cast_natCast] using
          jacobiDirichletCharacter_intCast q ((a.val : ℤ) - t)
      rw [hc]
      congr 1
      simpa only [Int.cast_natCast] using fourier_div_eq_stdAddChar_mul q h (a.val : ℤ)
    _ = ∑ a : ZMod q, jacobiDirichletCharacter q (a - (t : ZMod q)) *
        ZMod.stdAddChar ((h : ZMod q) * a) :=
      sum_fin_residues_eq_sum_zmod q (fun a =>
        jacobiDirichletCharacter q (a - (t : ZMod q)) *
          ZMod.stdAddChar ((h : ZMod q) * a))
    _ = _ := translated_jacobi_gauss_sum hq hsq h t

theorem translated_jacobi_divModEquiv (q : ℕ) [NeZero q] (m t : ℤ) :
    (jacobiSym (((Int.divModEquiv q m).2.val : ℤ) - t) q : ℂ) =
      (jacobiSym (m - t) q : ℂ) := by
  have hr : (Int.divModEquiv q m).1 * (q : ℤ) +
      ((Int.divModEquiv q m).2.val : ℤ) = m := (Int.divModEquiv q).symm_apply_apply m
  have hmod : (((Int.divModEquiv q m).2.val : ℕ) : ZMod q) = (m : ZMod q) := by
    have hz := congrArg (fun z : ℤ => (z : ZMod q)) hr
    simpa using hz
  rw [← jacobiDirichletCharacter_intCast, ← jacobiDirichletCharacter_intCast]
  simp only [Int.cast_sub, Int.cast_natCast, hmod]

theorem translated_quadratic_poisson {q : ℕ} [NeZero q]
    (hq : Odd q) (hsq : Squarefree q) (X : ℝ) (hX : 0 < X) (t : ℤ)
    (f : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, (jacobiSym (n - t) q : ℂ) * f ((n : ℝ) / X)) =
      ((X / q : ℝ) : ℂ) * gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar *
        ∑' h : ℤ, (jacobiSym h q : ℂ) *
          ZMod.stdAddChar ((h : ZMod q) * (t : ZMod q)) * 𝓕 f ((h : ℝ) * X / q) := by
  have hp := periodic_weighted_poisson_scaled q X hX
    (fun a : Fin q => (jacobiSym ((a.val : ℤ) - t) q : ℂ)) f
  simp_rw [translated_jacobi_divModEquiv,
    finite_translated_jacobi_gauss_transform hq hsq] at hp
  calc
    _ = ∑' h : ℤ, ((X / q : ℝ) : ℂ) *
        (ZMod.stdAddChar ((h : ZMod q) * (t : ZMod q)) * (jacobiSym h q : ℂ) *
          gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar) *
        𝓕 f ((h : ℝ) * X / q) := hp
    _ = ∑' h : ℤ,
        (((X / q : ℝ) : ℂ) * gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar) *
        ((jacobiSym h q : ℂ) * ZMod.stdAddChar ((h : ZMod q) * (t : ZMod q)) *
          𝓕 f ((h : ℝ) * X / q)) := by
      apply tsum_congr
      intro h
      ring
    _ = _ := tsum_mul_left

end Ostmann.QuadraticCenter

end OAI
