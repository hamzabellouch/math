import OAI.NumberTheory.CubicMoment.Estimates.CoreBlockGeometry

namespace OAI

/-! Numerical minimization of the two cubic-sieve orientations for an
outer frequency block. Variables p and q are the cube roots of its
squarefree side lengths. -/
namespace CubicFirstMoment

lemma outer_sieve_polynomial_min {p q j N T : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hj : p*q^2 ≤ j) (hN : 0 ≤ N) (hT : 0 ≤ T) :
    min (q^3*(p^3+N+p^2*T)) (p^3*(q^3+N+q^2*T)) ≤
      (p*q^2)*(j^2+N+j*T) := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hpq : 0 ≤ p*q^2 := mul_nonneg hp0 (sq_nonneg q)
  have hj0 : 0 ≤ j := hpq.trans hj
  have hq2 : q ≤ q^2 := by nlinarith
  have hq4 : q ≤ q^4 := hq2.trans (by nlinarith [sq_nonneg (q^2-1)])
  have hbase : p^2*q ≤ j^2 := by
    calc
      _ ≤ p^2*q^4 := mul_le_mul_of_nonneg_left hq4 (sq_nonneg p)
      _ = (p*q^2)^2 := by ring
      _ ≤ j^2 := pow_le_pow_left₀ hpq hj 2
  rcases le_total q p with hqp | hpq'
  · have hprod : p*q ≤ j := (mul_le_mul_of_nonneg_left hq2 hp0).trans hj
    have hmain := mul_le_mul_of_nonneg_left hbase hpq
    have hlinear : q^3*N ≤ (p*q^2)*N := by
      apply mul_le_mul_of_nonneg_right _ hN
      nlinarith [mul_le_mul_of_nonneg_right hqp (sq_nonneg q)]
    have hcross := mul_le_mul_of_nonneg_left hprod (mul_nonneg hpq hT)
    apply (min_le_left _ _).trans
    nlinarith
  · have hpq2 : p ≤ q^2 := hpq'.trans hq2
    have hprod : p^2 ≤ j := (by nlinarith [mul_le_mul_of_nonneg_left hpq2 hp0] : p^2 ≤ p*q^2).trans hj
    have hmain := mul_le_mul_of_nonneg_left hbase hpq
    have hlinear : p^3*N ≤ (p*q^2)*N := by
      apply mul_le_mul_of_nonneg_right _ hN
      nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp0 hpq' 2) hp0]
    have hcross := mul_le_mul_of_nonneg_left hprod (mul_nonneg hpq hT)
    apply (min_le_right _ _).trans
    nlinarith

end CubicFirstMoment

end OAI
