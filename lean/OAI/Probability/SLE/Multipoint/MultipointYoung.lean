import OAI.Probability.SLE.Multipoint.MultipointRegularizer

namespace OAI

/-! Weighted Young absorption for the pair terms in the multipoint
regularized product. The constant depends on the order and SLE parameter,
not the two target levels or their current clocks. -/

noncomputable section
namespace SLEExactGauge.Multipoint

def youngConstant (p C ε : ℝ) : ℝ :=
  (1-2*eta p) * (C*(eta p/ε)^(2*eta p))^(1/(1-2*eta p))

lemma youngConstant_pos {p C ε : ℝ} (hp : 0 < p) (hC : 0 < C) (hε : 0 < ε) :
    0 < youngConstant p C ε := by
  have he := eta_pos (p := p)
  have hr : 0 < 1-2*eta p := by linarith [eta_lt_half hp]
  unfold youngConstant
  positivity

lemma three_factor_young {p C ε x y z : ℝ} (hp : 0 < p)
    (hC : 0 < C) (hε : 0 < ε) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    C*x^(eta p)*y^(eta p)*z^(1-2*eta p) ≤
      ε*(x+y) + youngConstant p C ε*z := by
  let e := eta p
  let r := 1-2*e
  let b := ε/e
  let K := (C*(e/ε)^(2*e))^(1/r)
  have he : 0 < e := eta_pos
  have hr : 0 < r := by dsimp only [r, e]; linarith [eta_lt_half hp]
  have hb : 0 < b := div_pos hε he
  have hK : 0 < K := by dsimp only [K]; positivity
  have hKr : K^r = C*(e/ε)^(2*e) := by
    dsimp only [K]
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hr.ne', Real.rpow_one]
  have hcoef : b^e*b^e*K^r = C := by
    rw [← Real.rpow_add hb, show e+e = 2*e by ring, hKr]
    calc
      _ = C*(b^(2*e)*(e/ε)^(2*e)) := by ring
      _ = C*(b*(e/ε))^(2*e) := by rw [Real.mul_rpow hb.le (div_pos he hε).le]
      _ = C := by
        have hinv : b*(e/ε) = 1 := by dsimp only [b]; field_simp
        rw [hinv, Real.one_rpow, mul_one]
  have hprod : (b*x)^e*(b*y)^e*(K*z)^r = C*x^e*y^e*z^r := by
    rw [Real.mul_rpow hb.le hx, Real.mul_rpow hb.le hy, Real.mul_rpow hK.le hz]
    calc
      _ = (b^e*b^e*K^r)*(x^e*y^e*z^r) := by ring
      _ = _ := by rw [hcoef]; ring
  have hmean := Real.geom_mean_le_arith_mean3_weighted he.le he.le hr.le
    (mul_nonneg hb.le hx) (mul_nonneg hb.le hy) (mul_nonneg hK.le hz)
    (show e+e+r = 1 by dsimp only [r]; ring)
  rw [hprod] at hmean
  calc
    _ ≤ e*(b*x)+e*(b*y)+r*(K*z) := hmean
    _ = _ := by
      change e*(b*x)+e*(b*y)+r*(K*z) = ε*(x+y)+(r*K)*z
      dsimp only [b]
      field_simp

/-- The factor from the singular angular derivatives is absorbed with
coefficient ε at both vertices and a deterministic inverse-regulator cost. -/
theorem weighted_pair_absorption {p C ε D x y z : ℝ} (hp : 0 < p)
    (hC : 0 < C) (hε : 0 < ε) (hD : 0 < D)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    C*D^(-1-eta p)*x^(eta p)*y^(eta p)*z^(1-2*eta p) ≤
      ε*(x+y) + youngConstant p C ε*D^(-exponent p)*z := by
  have he := eta_pos (p := p)
  have hr : 0 < 1-2*eta p := by linarith [eta_lt_half hp]
  have hCD : 0 < C*D^(-1-eta p) := mul_pos hC (Real.rpow_pos_of_pos hD _)
  have hconst : youngConstant p (C*D^(-1-eta p)) ε =
      youngConstant p C ε*D^(-exponent p) := by
    unfold youngConstant
    have hb : 0 < C*(eta p/ε)^(2*eta p) := by positivity
    rw [show C*D^(-1-eta p)*(eta p/ε)^(2*eta p) =
      (C*(eta p/ε)^(2*eta p))*D^(-1-eta p) by ring,
      Real.mul_rpow hb.le (Real.rpow_pos_of_pos hD _).le,
      ← Real.rpow_mul hD.le]
    have hexp : (-1-eta p)*(1/(1-2*eta p)) = -exponent p := by
      unfold exponent
      ring
    rw [hexp]
    ring
  simpa only [hconst, mul_assoc] using three_factor_young hp hCD hε hx hy hz

end SLEExactGauge.Multipoint

end

end OAI
