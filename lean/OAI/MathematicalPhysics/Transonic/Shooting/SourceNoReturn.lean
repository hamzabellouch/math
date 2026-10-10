import OAI.MathematicalPhysics.Transonic.Shooting.Family
import OAI.MathematicalPhysics.Transonic.Shooting.ShootingBounds
import OAI.MathematicalPhysics.Transonic.Shooting.ClampedNoReturn

namespace OAI

section
noncomputable section

namespace SepticProfile.SonicShooting
open Set SourceFamily RegularContinuation IntegerPolynomial

lemma regular_outward (p : Parameter) {t : ℝ} (ht : t ∈ Icc (0:ℝ) (9/100)) :
    (-numer (kap p) (99/100-t) 0/denom (sig p) (99/100-t) 0)<0 ∧
    0<(-numer (kap p) (99/100-t) (999/1000)/denom (sig p) (99/100-t) (999/1000)) := by
  have hs : (sig p) ∈ Icc (0:ℝ) 1 := by
    have hb : 991/1000<sig p ∧ sig p<993/1000 := ShootingParameters.sigma_shooting_bounds p.property
    constructor <;> linarith [hb.1,hb.2]
  have hk : -(1/500:ℝ)<kap p ∧ kap p<0 := ShootingParameters.kappa_bounds p.property
  have hz : 99/100-t ∈ Icc (9/10:ℝ) (99/100) := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  constructor
  · apply div_neg_of_neg_of_pos _ (denom_pos hs hz (by norm_num))
    apply neg_neg_of_pos
    unfold numer
    simp only [pow_two, mul_zero, zero_div,sub_zero,mul_one]
    have hm := mul_pos (by linarith [hk.1] : 0<kap p+3) (by linarith [hz.1] : 0<99/100-t)
    nlinarith only [hm]
  · apply div_pos _ (denom_pos hs hz (by norm_num))
    apply neg_pos.mpr
    unfold numer
    apply mul_neg_of_pos_of_neg (by norm_num)
    have hm := mul_neg_of_neg_of_pos hk.2 (by linarith [hz.1] : 0<99/100-t)
    have hm' := mul_neg_of_neg_of_pos hm (by norm_num : (0:ℝ)<1-(999/1000)^2)
    linarith [hz.2]

theorem Family.regular_unclamped (F : Family) (p : Parameter)
    (hend : F.v p (9/100) ∈ Ioo (0:ℝ) (999/1000)) :
    (∀ t ∈ Icc (0:ℝ) (9/100), F.v p t ∈ Ioo (0:ℝ) (999/1000)) ∧
    ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt (F.v p)
      (-numer (kap p) (99/100-t) (F.v p t)/denom (sig p) (99/100-t) (F.v p t)) (Icc 0 (9/100)) t := by
  exact clamped_no_return (by norm_num : (0:ℝ)≤999/1000)
    (f:=fun q:ℝ×ℝ => -numer (kap p) (99/100-q.1) q.2/denom (sig p) (99/100-q.1) q.2)
    (F.v_der p) (fun t ht => (regular_outward p ht).1) (fun t ht => (regular_outward p ht).2) hend

lemma euler_outward (p : Parameter) {e t : ℝ} (he : 0<e) (helt : e<1/3)
    (ht : t ∈ Icc e (5/6)) :
    EulerContinuation.N (kap p) t 0/EulerContinuation.D (sig p) t 0<0 ∧
    0<EulerContinuation.N (kap p) t (1-e/1000)/EulerContinuation.D (sig p) t (1-e/1000) := by
  have hs : sig p<1 := by
    have hb : sig p<993/1000 := (ShootingParameters.sigma_shooting_bounds p.property).2
    linarith
  have hk : -(1/500:ℝ)<kap p ∧ kap p<0 := ShootingParameters.kappa_bounds p.property
  have ht' : t ∈ Icc (0:ℝ) (5/6) := ⟨he.le.trans ht.1,ht.2⟩
  have hb : 0<1-(1+1/500:ℝ)*t := by linarith [ht.2]
  have hc0 : 0<1-e/1000 := by linarith
  have hc1 : 1-e/1000<1 := by linarith
  have hc2 : 0<1-(1-e/1000)^2 := by nlinarith
  have hh : 1-(1+1/500:ℝ)*t-(1-t)*(1-e/1000)<0 := by
    have ht0 : 0<t := he.trans_le ht.1
    have hm : 0<e*t := mul_pos he ht0
    nlinarith [ht.1]
  constructor
  · apply div_neg_of_neg_of_pos _ (EulerContinuation.D_pos hs ht' (by norm_num))
    unfold EulerContinuation.N
    simp only [pow_two,mul_zero,sub_zero,mul_one]
    apply mul_neg_of_neg_of_pos (by norm_num)
    have hm := mul_pos (by linarith [hk.1] : 0<kap p+3) hb
    nlinarith only [hm]
  · apply div_pos _ (EulerContinuation.D_pos hs ht' ⟨hc0.le,hc1⟩)
    unfold EulerContinuation.N
    apply mul_pos_of_neg_of_neg
    · apply mul_neg_of_neg_of_pos (by norm_num)
      nlinarith
    · have hm := mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hk.2 hb) hc2
      linarith

theorem Family.euler_unclamped (F : Family) (p : Parameter)
    (hend : F.u p (5/6) ∈ Ioo (0:ℝ) (1-F.e/1000)) :
    (∀ t ∈ Icc F.e (5/6), F.u p t ∈ Ioo (0:ℝ) (1-F.e/1000)) ∧
    ∀ t ∈ Icc F.e (5/6), HasDerivWithinAt (F.u p)
      (EulerContinuation.N (kap p) t (F.u p t)/EulerContinuation.D (sig p) t (F.u p t)) (Icc F.e (5/6)) t := by
  apply clamped_no_return (by linarith [F.e_lt] : (0:ℝ)≤1-F.e/1000)
    (f:=fun q:ℝ×ℝ => EulerContinuation.N (kap p) q.1 q.2/EulerContinuation.D (sig p) q.1 q.2)
    (F.u_der p) (fun t ht => (euler_outward p F.e_pos F.e_lt ht).1)
    (fun t ht => (euler_outward p F.e_pos F.e_lt ht).2) hend

end SepticProfile.SonicShooting

end
end

end OAI
