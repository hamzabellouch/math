import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.ComplementFormLower

namespace OAI

/-! Scalar form estimates for replacing the manufactured density by point
nuclei. The complement norm can be the full H1 norm rather than L2 mass. -/

noncomputable section
namespace ContinuumCoulomb

theorem coercive_complement_scalar_lower {F P Q a g C p q q₁ c : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hq₁ : 0 ≤ q₁) (hg : 0 < g) (hC : 0 ≤ C)
    (hm : P+Q+2*c ≤ F) (hP : a*p ≤ P) (hQ : a*q+g*q₁ ≤ Q)
    (hc : c^2 ≤ C*p*q₁) :
    (a-C/g)*(p+q) ≤ F := by
  have ha := absorb_cross_term hC hp hq₁ hg hc
  have he : 0 ≤ (C/g)*q := mul_nonneg (div_nonneg hC hg.le) hq
  nlinarith only [hm,hP,hQ,ha,he]

theorem three_mixed_square_bound {a b c A B C p q : ℝ}
    (ha : a^2 ≤ A*p*q) (hb : b^2 ≤ B*p*q) (hc : c^2 ≤ C*p*q) :
    (a+b+c)^2 ≤ 3*(A+B+C)*p*q := by
  nlinarith only [ha,hb,hc,sq_nonneg (a-b),sq_nonneg (a-c),sq_nonneg (b-c)]

theorem perturbed_coercive_complement {Q E a g δ p q : ℝ}
    (hq : 0 ≤ q) (hqp : q ≤ p)
    (hQ : g*p ≤ Q-E*q) (herr : |δ| ≤ a*p) :
    (g-a-|E|)*p ≤ Q+δ := by
  have he := mul_le_mul_of_nonneg_left hqp (abs_nonneg E)
  have heq := mul_le_mul_of_nonneg_right (neg_abs_le E) hq
  have hd := (abs_le.mp herr).1
  nlinarith only [hQ,he,heq,hd]

end ContinuumCoulomb

end

end OAI
