import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMixedMoment

namespace OAI

/-! Exact prime-power times cofactor polynomial identity. This attaches
the proved mixed coefficient estimate to the actual expression used on
the multiscale large-prime frequency classes. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_multiplicative_phase {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (t : ℝ) :
    Complex.exp (((-Real.log (m : ℝ) * t : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((-Real.log (n : ℝ) * t : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((-Real.log ((m * n : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add, Nat.cast_mul, Real.log_mul
    (by exact_mod_cast hm.ne') (by exact_mod_cast hn.ne')]
  congr 1
  push_cast
  ring

lemma mrt_mixed_tuple_term {r : ℕ} (v : Fin r → ℕ)
    (hv : ∀ i, 0 < v i) {m : ℕ} (hm : 0 < m) (a b : ℕ → ℂ) (t : ℝ) :
    (∏ i, (a (v i) / (v i : ℂ)) *
      Complex.exp (((-Real.log (v i : ℝ) * t : ℝ) : ℂ) * Complex.I)) *
      ((b m / (m : ℂ)) *
        Complex.exp (((-Real.log (m : ℝ) * t : ℝ) : ℂ) * Complex.I)) =
      ((∏ i, a (v i)) * b m) / ((∏ i, v i) * m : ℕ) *
        Complex.exp (((-Real.log (((∏ i, v i) * m : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
  rw [prod_mul_distrib, prod_div_distrib, mrt_prime_tuple_phase v hv t]
  have hprod : 0 < ∏ i, v i := prod_pos (fun i _ => hv i)
  have he := mrt_multiplicative_phase hprod hm t
  rw [← he]
  push_cast
  ring

theorem mrt_mixed_polynomial_identity (P M : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hM : ∀ m ∈ M, 0 < m)
    (a b : ℕ → ℂ) (r L U : ℕ)
    (hsupport : ∀ v ∈ Fintype.piFinset (fun _ : Fin r => P), ∀ m ∈ M,
      L < (∏ i, v i) * m ∧ (∏ i, v i) * m ≤ U) (t : ℝ) :
    (mrtExponentialPolynomial P (fun p => a p / (p : ℂ))
      (fun p => -Real.log (p : ℝ)) t) ^ r *
      mrtExponentialPolynomial M (fun m => b m / (m : ℂ))
        (fun m => -Real.log (m : ℝ)) t =
      mrtExponentialPolynomial (Ioc L U)
        (fun n => mrtMixedPrimeCoefficient P M a b r n / (n : ℂ))
        (fun n => -Real.log (n : ℝ)) t := by
  let V := Fintype.piFinset (fun _ : Fin r => P)
  let S := V ×ˢ M
  let mult : ((Fin r → ℕ) × ℕ) → ℕ := fun v => (∏ i, v.1 i) * v.2
  let coeff : ((Fin r → ℕ) × ℕ) → ℂ := fun v => (∏ i, a (v.1 i)) * b v.2
  let term : ℕ → ℂ := fun n => (n : ℂ)⁻¹ *
    Complex.exp (((-Real.log (n : ℝ) * t : ℝ) : ℂ) * Complex.I)
  have hmap : ∀ v ∈ S, mult v ∈ Ioc L U := by
    intro v hv
    exact mem_Ioc.mpr (hsupport v.1 (mem_product.mp hv).1 v.2 (mem_product.mp hv).2)
  have hgroup : (∑ n ∈ Ioc L U, ∑ v ∈ S.filter (fun v => mult v = n),
      coeff v * term (mult v)) = ∑ v ∈ S, coeff v * term (mult v) :=
    sum_fiberwise_of_maps_to hmap _
  have hright : mrtExponentialPolynomial (Ioc L U)
      (fun n => mrtMixedPrimeCoefficient P M a b r n / (n : ℂ))
      (fun n => -Real.log (n : ℝ)) t = ∑ v ∈ S, coeff v * term (mult v) := by
    rw [← hgroup]
    unfold mrtExponentialPolynomial mrtMixedPrimeCoefficient mrtMixedPrimeFiber
    apply sum_congr rfl
    intro n _
    simp only [sum_div, sum_mul]
    apply sum_congr rfl
    intro v hv
    have he : mult v = n := (mem_filter.mp hv).2
    change coeff v / (n : ℂ) * _ = coeff v * term (mult v)
    rw [he]
    dsimp [term]
    ring
  rw [hright]
  unfold mrtExponentialPolynomial
  rw [sum_pow', sum_mul]
  simp_rw [mul_sum]
  rw [sum_product]
  apply sum_congr rfl
  intro v hv
  apply sum_congr rfl
  intro m hm
  simpa only [coeff, term, mult, div_eq_mul_inv, mul_assoc] using
    mrt_mixed_tuple_term v
      (fun i => (hP _ (Fintype.mem_piFinset.mp hv i)).pos) (hM m hm) a b t

theorem mrt_mixed_prime_cofactor_mean_square (P M : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hM : ∀ m ∈ M, 0 < m)
    (a b : ℕ → ℂ) (ha : ∀ p ∈ P, ‖a p‖ ≤ 1) (hb : ∀ m ∈ M, ‖b m‖ ≤ 1)
    (r : ℕ) {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U)
    (hsupport : ∀ v ∈ Fintype.piFinset (fun _ : Fin r => P), ∀ m ∈ M,
      L < (∏ i, v i) * m ∧ (∏ i, v i) * m ≤ U)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖(mrtExponentialPolynomial P (fun p => a p / (p : ℂ))
      (fun p => -Real.log (p : ℝ)) t) ^ r *
        mrtExponentialPolynomial M (fun m => b m / (m : ℂ))
          (fun m => -Real.log (m : ℝ)) t‖ ^ 2) ≤
      16 * Real.exp 1 * ((T + U) / (L : ℝ)) * (r.factorial : ℝ) ^ 2 *
        (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) ^ 3 := by
  simp_rw [mrt_mixed_polynomial_identity P M hP hM a b r L U hsupport]
  exact mrt_mixed_coefficient_mean_square P M hP a b ha hb r hL hLU hT

end TwoPointCorrelations

end OAI
