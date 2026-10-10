import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEisenstein

namespace OAI

/-! A positive quadratic majorant for the initial cubic Eisenstein series.
This supplies actual convergence, rather than relying on formal reindexing. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaHeightConstant (p : ℂ × ℝ) : ℝ :=
  2*(2+(1+2*Complex.normSq p.1)/p.2^2)

lemma cubicThetaHeightConstant_pos {p : ℂ × ℝ} (hp : 0 < p.2) :
    0 < cubicThetaHeightConstant p := by
  have hz := Complex.normSq_nonneg p.1
  unfold cubicThetaHeightConstant
  positivity

private lemma normSq_sub_le (a b : ℂ) :
    Complex.normSq (a-b) ≤ 2*Complex.normSq a+2*Complex.normSq b := by
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  nlinarith [sq_nonneg (a.re+b.re),sq_nonneg (a.im+b.im)]

lemma CubicThetaBottomRow.norm_le_denominator (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 0 < p.2) :
    1+norm r.c+norm r.d ≤ cubicThetaHeightConstant p*
      (Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2) := by
  let D := Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2
  have hv := sq_pos_of_pos hp
  have hD : 0 ≤ D := add_nonneg (Complex.normSq_nonneg _)
    (mul_nonneg (norm_nonneg _) (sq_nonneg _))
  have hc : norm r.c ≤ D/p.2^2 := by
    apply (le_div_iff₀ hv).mpr
    dsimp [D]
    linarith [Complex.normSq_nonneg ((r.c:ℂ)*p.1+r.d)]
  have hd : norm r.d ≤ 2*Complex.normSq ((r.c:ℂ)*p.1+r.d)+
      2*norm r.c*Complex.normSq p.1 := by
    have h := normSq_sub_le ((r.c:ℂ)*p.1+r.d) ((r.c:ℂ)*p.1)
    rw [add_sub_cancel_left,Complex.normSq_mul] at h
    simpa only [norm,mul_assoc] using h
  have hn : norm r.c+norm r.d ≤ (2+(1+2*Complex.normSq p.1)/p.2^2)*D := by
    calc
      _ ≤ 2*Complex.normSq ((r.c:ℂ)*p.1+r.d)+(1+2*Complex.normSq p.1)*norm r.c := by linarith
      _ ≤ 2*D+(1+2*Complex.normSq p.1)*(D/p.2^2) := by
        apply add_le_add
        · dsimp [D]
          have h := mul_nonneg (norm_nonneg r.c) (sq_nonneg p.2)
          linarith
        · exact mul_le_mul_of_nonneg_left hc (by linarith [Complex.normSq_nonneg p.1])
      _ = _ := by ring
  have hd1 := one_le_norm (primary_ne_zero r.d_primary)
  change 1+norm r.c+norm r.d ≤ 2*(2+(1+2*Complex.normSq p.1)/p.2^2)*D
  nlinarith [norm_nonneg r.c]

lemma CubicThetaBottomRow.height_le (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 0 < p.2) :
    r.height p ≤ (p.2*cubicThetaHeightConstant p)/(1+norm r.c+norm r.d) := by
  have hN : 0 < 1+norm r.c+norm r.d := by linarith [norm_nonneg r.c,norm_nonneg r.d]
  have hD : 0 < Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2 := by
    have h := r.height_pos hp
    exact (div_pos_iff.mp h).resolve_right (fun hh => (not_lt_of_ge hp.le) hh.1) |>.2
  apply (div_le_div_iff₀ hD hN).mpr
  have h := mul_le_mul_of_nonneg_left (r.norm_le_denominator hp) hp.le
  convert h using 1
  ring

lemma cubicTheta_two_norm_decay {a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ s) :
    (1+a+b)^(-s) ≤ (1+a)^(-s/2)*(1+b)^(-s/2) := by
  have hA : 0 < 1+a := by positivity
  have hB : 0 < 1+b := by positivity
  have hL : 0 < 1+a+b := by positivity
  have hprod : (1+a)*(1+b) ≤ (1+a+b)^2 := by nlinarith [mul_nonneg ha hb]
  calc
    _ = ((1+a+b)^2)^(-s/2) := by
      rw [←Real.rpow_natCast_mul hL.le]
      congr 1
      ring
    _ ≤ ((1+a)*(1+b))^(-s/2) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos hA hB) hprod (by linarith)
    _ = _ := Real.mul_rpow hA.le hB.le

end CubicFirstMoment

end

end OAI
