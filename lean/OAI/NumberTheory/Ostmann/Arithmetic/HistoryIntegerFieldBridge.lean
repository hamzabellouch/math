import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFieldEvaluation

namespace OAI

noncomputable section
namespace Ostmann.Characters.RationalHistory.Expr
open MvPolynomial
variable {ι : Type*}

theorem eval₂_cast_int {K : Type*} [CommRing K] (P : MvPolynomial ι ℤ) (x : ι → ℤ) :
    eval₂ (Int.castRingHom K) (fun i => (x i : K)) P = (eval x P : K) :=
  (MvPolynomial.eval₂_comp (Int.castRingHom K) x P).symm

@[simp] theorem fieldEval_rat (e : Expr ι) (x : ι → ℚ) :
    e.fieldEval x = e.rationalEval x := by
  induction e <;> simp_all only [fieldEval, rationalEval]

@[simp] theorem fieldRegularAt_rat (e : Expr ι) (x : ι → ℚ) :
    e.FieldRegularAt x ↔ e.RegularAt x := by
  induction e <;> simp_all only [FieldRegularAt, RegularAt, fieldEval_rat]

theorem integer_cleared_of_rational_eq (e : Expr ι) (x : ι → ℤ) (n : ℤ)
    (hQ : e.RegularAt (fun i => (x i : ℚ)))
    (he : e.rationalEval (fun i => (x i : ℚ)) = (n : ℚ)) :
    eval x e.denominator * n = eval x e.numerator := by
  have hh := (e.rational_cleared (fun i => (x i : ℚ)) hQ).2
  rw [he, eval₂_cast_int, eval₂_cast_int] at hh
  apply Int.cast_injective (α := ℚ)
  simpa only [Int.cast_mul] using hh

theorem fieldEval_eq_int_of_cleared {K : Type*} [Field K]
    (e : Expr ι) (x : ι → ℤ) (n : ℤ)
    (hK : e.FieldRegularAt (fun i => (x i : K)))
    (he : eval x e.denominator * n = eval x e.numerator) :
    e.fieldEval (fun i => (x i : K)) = (n : K) := by
  obtain ⟨hd, hv⟩ := e.field_cleared (fun i => (x i : K)) hK
  rw [eval₂_cast_int] at hd
  rw [eval₂_cast_int, eval₂_cast_int] at hv
  have hc : (eval x e.denominator : K) * (n : K) = (eval x e.numerator : K) := by
    simpa only [Int.cast_mul] using congrArg (fun z : ℤ => (z : K)) he
  exact mul_left_cancel₀ hd (hv.trans hc.symm)

theorem fieldEval_eq_int_of_rational_eq {K : Type*} [Field K]
    (e : Expr ι) (x : ι → ℤ) (n : ℤ)
    (hQ : e.RegularAt (fun i => (x i : ℚ)))
    (he : e.rationalEval (fun i => (x i : ℚ)) = (n : ℚ))
    (hK : e.FieldRegularAt (fun i => (x i : K))) :
    e.fieldEval (fun i => (x i : K)) = (n : K) :=
  e.fieldEval_eq_int_of_cleared x n hK (e.integer_cleared_of_rational_eq x n hQ he)

theorem fieldEval_eq_integerEval {K : Type*} [Field K]
    (e : Expr ι) (x : ι → ℤ) (hI : e.IntegralAt x)
    (hK : e.FieldRegularAt (fun i => (x i : K))) :
    e.fieldEval (fun i => (x i : K)) = (e.integerEval x : K) :=
  e.fieldEval_eq_int_of_cleared x (e.integerEval x) hK (e.integerEval_cleared x hI)

theorem eval₂_cast_int_zmod_eq_zero_iff (P : MvPolynomial ι ℤ) (x : ι → ℤ) (p : ℕ) :
    eval₂ (Int.castRingHom (ZMod p)) (fun i => (x i : ZMod p)) P = 0 ↔
      (p : ℤ) ∣ eval x P := by
  rw [eval₂_cast_int, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem eval₂_cast_int_ne_zero_of_not_dvd (P : MvPolynomial ι ℤ) (x : ι → ℤ) (p : ℕ)
    (h : ¬ (p : ℤ) ∣ eval x P) :
    eval₂ (Int.castRingHom (ZMod p)) (fun i => (x i : ZMod p)) P ≠ 0 :=
  fun hz => h ((eval₂_cast_int_zmod_eq_zero_iff P x p).mp hz)

end Ostmann.Characters.RationalHistory.Expr

end

end OAI
