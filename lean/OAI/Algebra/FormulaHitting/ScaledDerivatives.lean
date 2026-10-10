import OAI.Algebra.FormulaHitting.Wronskian
import OAI.Algebra.FormulaHitting.NumeratorRows

namespace OAI

noncomputable section

namespace NCHitting

open PowerSeries Polynomial Matrix

variable {F : Type*} [Field F]
variable {I : Type*} [Fintype I]

theorem derivative_scaled_power (q f : PowerSeries F) (j : ℕ) :
    q * PowerSeries.derivative (R := F) (q^j * f) =
      (j : PowerSeries F) * PowerSeries.derivative (R := F) q * (q^j * f) +
        q^(j+1) * PowerSeries.derivative (R := F) f := by
  rw [Derivation.leibniz]
  cases j with
  | zero => simp
  | succ j =>
    rw [PowerSeries.derivative_pow]
    simp only [Nat.add_sub_cancel, smul_eq_mul, pow_succ]
    ring

theorem coePolynomial_sum (Z : I → F[X]) :
    ((∑ t : I, Z t : F[X]) : PowerSeries F) = ∑ t : I, (Z t : PowerSeries F) :=
  map_sum Polynomial.coeToPowerSeries.ringHom Z Finset.univ

theorem coePolynomial_sub (p q : F[X]) :
    ((p - q : F[X]) : PowerSeries F) = (p : PowerSeries F) - (q : PowerSeries F) :=
  map_sub Polynomial.coeToPowerSeries.ringHom p q

theorem coePolynomial_natCast (k : ℕ) :
    ((k : F[X]) : PowerSeries F) = (k : PowerSeries F) :=
  map_natCast Polynomial.coeToPowerSeries.ringHom k

theorem derivative_polynomial_row (q : F[X]) (P : Matrix I I F[X])
    (G : Matrix I I (PowerSeries F))
    (hG : ∀ t l, (q : PowerSeries F) * PowerSeries.derivative (R := F) (G t l) =
      ∑ a : I, (P t a : PowerSeries F) * G a l)
    (Z : I → F[X]) (l : I) :
    (q : PowerSeries F) * PowerSeries.derivative (R := F)
        (∑ t : I, (Z t : PowerSeries F) * G t l) =
      ∑ t : I, ((q * (Z t).derivative + ∑ a : I, Z a * P a t : F[X]) :
        PowerSeries F) * G t l := by
  classical
  calc
    _ = ∑ t : I, (((q : PowerSeries F) * ((Z t).derivative : PowerSeries F)) * G t l +
          (Z t : PowerSeries F) * ((q : PowerSeries F) * PowerSeries.derivative (R := F) (G t l))) := by
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [Derivation.leibniz, PowerSeries.derivative_coe]
      simp only [smul_eq_mul]
      ring
    _ = ∑ t : I, (((q : PowerSeries F) * ((Z t).derivative : PowerSeries F)) * G t l +
          ∑ a : I, (Z t : PowerSeries F) * (P t a : PowerSeries F) * G a l) := by
      simp_rw [hG, Finset.mul_sum, mul_assoc]
    _ = _ := by
      simp only [Polynomial.coe_add, Polynomial.coe_mul, coePolynomial_sum,
        add_mul, Finset.sum_mul, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]

theorem scaled_derivative_row (q : F[X]) (P : Matrix I I F[X]) (u : I → F)
    (G : Matrix I I (PowerSeries F))
    (hG : ∀ t l, (q : PowerSeries F) * PowerSeries.derivative (R := F) (G t l) =
      ∑ a : I, (P t a : PowerSeries F) * G a l)
    (j : ℕ) (l : I) :
    (q : PowerSeries F)^j * derivativeIter j
        (∑ t : I, PowerSeries.C (u t) * G t l) =
      ∑ t : I, (numeratorRow q P u j t : PowerSeries F) * G t l := by
  classical
  induction j with
  | zero => simp [derivativeIter, numeratorRow]
  | succ j ih =>
    have hd := congrArg (fun f : PowerSeries F =>
      (q : PowerSeries F) * PowerSeries.derivative (R := F) f) ih
    rw [derivative_scaled_power, derivative_polynomial_row q P G hG] at hd
    have he := eq_sub_of_add_eq' hd
    change (q : PowerSeries F)^(j+1) * PowerSeries.derivative (R := F)
      (derivativeIter j (∑ t : I, PowerSeries.C (u t) * G t l)) = _
    rw [he, ih]
    simp only [numeratorRow, Polynomial.coe_add, coePolynomial_sub,
      Polynomial.coe_mul, coePolynomial_sum,
      PowerSeries.derivative_coe, Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, add_mul, sub_mul, map_natCast, coePolynomial_natCast]
    simp only [mul_comm, mul_left_comm, mul_assoc]
    ring

end NCHitting

end

end OAI
