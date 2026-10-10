import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PolynomialResidualBudget

namespace OAI

/-! The amplified matrix error decays after retaining the smallness of
the shifted matrix in the change of basis. -/

noncomputable section
namespace ContinuumCoulomb

theorem logarithmic_separation_overlap {N D : ℝ} (hN : 2 ≤ N) (k : ℕ)
    (hD : 25*(k:ℝ)*Real.log N ≤ D) :
    Real.exp (-(9/10:ℝ)*D) ≤ ((N^k)^22)⁻¹ := by
  have hN0 : 0 < N := by linarith
  have hklog : 0 ≤ (k:ℝ)*Real.log N :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
  have he := Real.exp_le_exp.mpr
    (show -(9/10:ℝ)*D ≤ -22*(k:ℝ)*Real.log N by nlinarith only [hD,hklog])
  apply he.trans_eq
  rw [show -22*(k:ℝ)*Real.log N = -((22*k:ℕ):ℝ)*Real.log N by push_cast; ring,
    neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log hN0]
  congr 1
  rw [← pow_mul]
  congr 1
  omega

private theorem matrix_monomial_bound {R m c : ℝ} {p q : ℕ}
    (hR : 1 ≤ R) (hm : 0 ≤ m) (hc : 0 ≤ c) (hp : p ≤ 5) (hq : 2 ≤ q) :
    c*m^p/R^q ≤ c*(m+1)^5/R^2 := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hm5 : m^p ≤ (m+1)^5 := (pow_le_pow_left₀ hm (by linarith) p).trans
    (pow_le_pow_right₀ (by linarith) hp)
  exact div_le_div₀ (show 0 ≤ c*(m+1)^5 by positivity)
    (mul_le_mul_of_nonneg_left hm5 hc) (pow_pos hR0 _)
    (pow_le_pow_right₀ hR hq)

theorem one_body_scale_identity {R a d E P O W m : ℝ}
    (hR : R ≠ 0) (ha : a ≠ 0) :
    let δ := d*m/(a*R^30)
    let B := (W*O+m*P)/R^22+m*δ*P
    (a*R^30)*(4*m^2/R^32+m^2*(4*(2*m*(O/R^22))*B)+4*m^2*(E*(m+1)/R^32))+
      (a*R^30*m*P+m^2*d*P)/R^40+m^2*d*(W*O)/R^22 =
    (4*a)*m^2/R^2+(4*a*E)*m^3/R^2+(4*a*E)*m^2/R^2+
      (8*a*W*O^2)*m^3/R^14+(8*a*O*P)*m^4/R^14+
      (8*d*O*P)*m^5/R^22+(a*P)*m/R^10+(d*P)*m^2/R^40+
      (d*W*O)*m^2/R^22 := by
  dsimp only
  field_simp [hR,ha]
  ring

theorem one_body_scale_bound {R a d E P O W m : ℝ}
    (hR : 1 ≤ R) (ha : 0 < a) (hd : 0 ≤ d) (hE : 0 ≤ E)
    (hP : 0 ≤ P) (hO : 0 ≤ O) (hW : 0 ≤ W) (hm : 0 ≤ m) :
    let δ := d*m/(a*R^30)
    let B := (W*O+m*P)/R^22+m*δ*P
    (a*R^30)*(4*m^2/R^32+m^2*(4*(2*m*(O/R^22))*B)+4*m^2*(E*(m+1)/R^32))+
      (a*R^30*m*P+m^2*d*P)/R^40+m^2*d*(W*O)/R^22 ≤
    (4*a+8*a*E+8*a*W*O^2+8*a*O*P+8*d*O*P+a*P+d*P+d*W*O)*(m+1)^5/R^2 := by
  dsimp only
  rw [one_body_scale_identity (ne_of_gt (lt_of_lt_of_le zero_lt_one hR)) (ne_of_gt ha)]
  have h1 := matrix_monomial_bound (p := 2) (q := 2) hR hm (show 0 ≤ 4*a by positivity) (by decide) (by decide)
  have h2 := matrix_monomial_bound (p := 3) (q := 2) hR hm (show 0 ≤ 4*a*E by positivity) (by decide) (by decide)
  have h3 := matrix_monomial_bound (p := 2) (q := 2) hR hm (show 0 ≤ 4*a*E by positivity) (by decide) (by decide)
  have h4 := matrix_monomial_bound (p := 3) (q := 14) hR hm (show 0 ≤ 8*a*W*O^2 by positivity) (by decide) (by decide)
  have h5 := matrix_monomial_bound (p := 4) (q := 14) hR hm (show 0 ≤ 8*a*O*P by positivity) (by decide) (by decide)
  have h6 := matrix_monomial_bound (p := 5) (q := 22) hR hm (show 0 ≤ 8*d*O*P by positivity) (by decide) (by decide)
  have h7 := matrix_monomial_bound (p := 1) (q := 10) hR hm (show 0 ≤ a*P by positivity) (by decide) (by decide)
  have h8 := matrix_monomial_bound (p := 2) (q := 40) hR hm (show 0 ≤ d*P by positivity) (by decide) (by decide)
  have h9 := matrix_monomial_bound (p := 2) (q := 22) hR hm (show 0 ≤ d*W*O by positivity) (by decide) (by decide)
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5) h6) h7) h8) h9
  simp only [pow_one] at hsum
  exact hsum.trans_eq (by ring)

end ContinuumCoulomb

end

end OAI
