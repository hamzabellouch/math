import OAI.Algebra.DepthFive.MixedOperator

namespace OAI

/-! Weighted-degree preservation for differential/multiplication substitution. -/

noncomputable section

namespace Problem335

open MvPolynomial

variable {K σ M : Type*} [CommSemiring K] [AddCommGroup M]

/-- A partial derivative subtracts the weight of its variable. The use of a
weight group avoids artificial truncation at degree zero. -/
theorem pderiv_isWeightedHomogeneous {w : σ → M} {p : MvPolynomial σ K}
    {a : M} (hp : p.IsWeightedHomogeneous w a) (i : σ) :
    (pderiv i p).IsWeightedHomogeneous w (a - w i) := by
  intro d hd
  have hc : p.coeff (d + Finsupp.single i 1) ≠ 0 := by
    intro h
    apply hd
    rw [coeff_pderiv, h, zero_mul]
  have hw := hp hc
  rw [map_add, Finsupp.weight_single, one_nsmul] at hw
  exact eq_sub_iff_add_eq.mpr hw

/-- The weighted-degree shift assigned to an operator variable: differentiation
has negative weight, while multiplication has positive weight. -/
def operatorWeight (isV : σ → Bool) (w : σ → M) (i : σ) : M :=
  if isV i then -w i else w i

theorem variableOperator_isWeightedHomogeneous (isV : σ → Bool) {w : σ → M}
    {p : MvPolynomial σ K} {a : M} (hp : p.IsWeightedHomogeneous w a) (i : σ) :
    (variableOperator isV i p).IsWeightedHomogeneous w (a + operatorWeight isV w i) := by
  cases hi : isV i
  · simpa [variableOperator, operatorWeight, hi, add_comm] using
      (isWeightedHomogeneous_X (R := K) w i).mul hp
  · simpa [variableOperator, operatorWeight, hi, sub_eq_add_neg] using
      pderiv_isWeightedHomogeneous hp i

/-- A power of a variable shifts degree by the corresponding multiple. -/
theorem mixedOperator_X_pow_isWeightedHomogeneous (isV : σ → Bool) (w : σ → M)
    (i : σ) (r : ℕ) {p : MvPolynomial σ K} {a : M}
    (hp : p.IsWeightedHomogeneous w a) :
    (mixedOperator isV (X i ^ r) p).IsWeightedHomogeneous w
      (a + r • operatorWeight isV w i) := by
  induction r with
  | zero => simpa using hp
  | succ r ih =>
    rw [pow_succ', mixedOperator_mul_apply, mixedOperator_X]
    simpa [succ_nsmul, add_assoc, add_comm, add_left_comm] using
      variableOperator_isWeightedHomogeneous isV ih i

/-- Monomial operators shift weighted degree by the sum of their variable shifts. -/
theorem mixedOperator_monomial_one_isWeightedHomogeneous (isV : σ → Bool) (w : σ → M)
    (d : σ →₀ ℕ) {p : MvPolynomial σ K} {a : M}
    (hp : p.IsWeightedHomogeneous w a) :
    (mixedOperator isV (monomial d 1) p).IsWeightedHomogeneous w
      (a + Finsupp.weight (operatorWeight isV w) d) := by
  induction d using Finsupp.induction_linear generalizing p a with
  | zero => simpa using hp
  | add d e hd he =>
    rw [show monomial (d + e) (1 : K) = monomial d 1 * monomial e 1 by
      rw [monomial_mul_monomial, one_mul]]
    rw [mixedOperator_mul_apply]
    simpa [map_add, add_assoc, add_comm, add_left_comm] using hd (he hp)
  | single i r =>
    rw [← X_pow_eq_monomial]
    simpa [Finsupp.weight_single] using
      mixedOperator_X_pow_isWeightedHomogeneous isV w i r hp

/-- The full mixed operator sends homogeneous inputs to the degree obtained by
adding the (signed) homogeneous degree of its defining polynomial. -/
theorem mixedOperator_isWeightedHomogeneous (isV : σ → Bool) (w : σ → M)
    {q p : MvPolynomial σ K} {d a : M}
    (hq : q.IsWeightedHomogeneous (operatorWeight isV w) d)
    (hp : p.IsWeightedHomogeneous w a) :
    (mixedOperator isV q p).IsWeightedHomogeneous w (a + d) := by
  induction hq using IsWeightedHomogeneous.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]; exact isWeightedHomogeneous_zero _ _ _
  | add q r hq hr iq ir =>
    simpa only [map_add, LinearMap.add_apply] using iq.add ir
  | monomial e c he =>
    have hm := mixedOperator_monomial_one_isWeightedHomogeneous isV w e hp
    rw [he] at hm
    have heq : monomial e c = C c * monomial e (1 : K) := by rw [C_mul_monomial, mul_one]
    rw [heq, mixedOperator_mul_apply, mixedOperator_C]
    change (c • mixedOperator isV (monomial e 1) p).IsWeightedHomogeneous w (a + d)
    simpa only [C_mul'] using hm.C_mul c

end Problem335

end

end OAI
