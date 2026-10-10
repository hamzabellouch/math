import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeTailCost

namespace OAI

/-! The full discarded-amplitude error is smaller than L^-19 for the
source's allowed amplitude growth, uniformly over the level cutoffs. -/
noncomputable section
open Filter
namespace LipschitzHilbert

theorem retainedAmplitudeCost_le_linear (C0 L : ℝ) (hL : 1≤L) :
    retainedAmplitudeCost C0 (L/4)≤
      (4*Real.sqrt 2*Real.sqrt (4*C0)*(2/Real.log 2+5))*L := by
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hLp : 0≤L := by linarith
  have hT : 1≤2*((L/4)/Real.log 2)+5 := by
    have h : 0≤2*((L/4)/Real.log 2) := by positivity
    linarith
  have hs := Real.sqrt_le_self_iff.mpr (Or.inr hT)
  have ht : 2*((L/4)/Real.log 2)+5≤(2/Real.log 2+5)*L := by
    have hr : (L/4)/Real.log 2≤L/Real.log 2 :=
      div_le_div_of_nonneg_right (by linarith) hlog.le
    calc
      _≤2*(L/Real.log 2)+5 := by linarith
      _≤(2/Real.log 2+5)*L := by
        have he : 2*(L/Real.log 2)=(2/Real.log 2)*L := by ring
        rw [he]
        nlinarith
  unfold retainedAmplitudeCost
  calc
    _=(4*Real.sqrt 2*Real.sqrt (4*C0))*Real.sqrt (2*((L/4)/Real.log 2)+5) := by ring
    _≤(4*Real.sqrt 2*Real.sqrt (4*C0))*((2/Real.log 2+5)*L) :=
      mul_le_mul_of_nonneg_left (hs.trans ht) (by positivity)
    _=_ := by ring

theorem eventually_amplitude_error_decay (A B C0 : ℝ) (hA : 0<A) (hB : 0≤B) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℝ, 0≤Q → Q≤A*Real.exp (B*L^(9/10:ℝ)) →
      amplitudeTailCost Q L*(retainedAmplitudeCost C0 (L/4)+amplitudeTailCost Q L)+
        (retainedAmplitudeCost C0 (L/4)+amplitudeTailCost Q L)*amplitudeTailCost Q L≤L^(-19:ℝ) := by
  let D := 4*Real.sqrt 2*Real.sqrt (4*C0)*(2/Real.log 2+5)
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0≤D := by dsimp only [D]; positivity
  let delta := 1/(2*(D+1))
  have hd : 0<delta := by dsimp only [delta]; positivity
  have hsmall := (isLittleO_exp_neg_mul_rpow_atTop (by norm_num : (0:ℝ)<1/16) (-20)).bound hd
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_amplitudeTailCost_bound A B hA hB,hsmall]
    with L hL htail hsmall Q hQ hQbound
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hcost : retainedAmplitudeCost C0 (L/4)≤D*L := retainedAmplitudeCost_le_linear C0 L hL
  have he : Real.exp (-L/16)≤delta*L^(-20:ℝ) := by
    have heq : -(1/16:ℝ)*L=-L/16 := by ring
    simpa only [heq,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (Real.rpow_nonneg hLp.le (-20:ℝ))] using hsmall
  have heone : Real.exp (-L/16)≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have ht := htail Q hQbound
  have ht0 := amplitudeTailCost_nonneg Q L hQ
  have hr0 := retainedAmplitudeCost_nonneg C0 (L/4)
  have hp : L^(-20:ℝ)*L=L^(-19:ℝ) := by
    calc
      _=L^(-20:ℝ)*L^(1:ℝ) := by rw [Real.rpow_one]
      _=L^((-20:ℝ)+1) := (Real.rpow_add hLp _ _).symm
      _=_ := by norm_num
  calc
    _≤2*Real.exp (-L/16)*(D*L+1) := by
      have hs : retainedAmplitudeCost C0 (L/4)+amplitudeTailCost Q L≤D*L+1 :=
        add_le_add hcost (ht.trans heone)
      have hp1 := mul_le_mul ht hs (add_nonneg hr0 ht0) (Real.exp_pos _).le
      have hp2 := mul_le_mul hs ht ht0 (by positivity : 0≤D*L+1)
      nlinarith
    _≤2*(delta*L^(-20:ℝ))*((D+1)*L) := by
      have hlin : D*L+1≤(D+1)*L := by nlinarith
      exact mul_le_mul (mul_le_mul_of_nonneg_left he (by norm_num)) hlin
        (by positivity) (by positivity)
    _=L^(-19:ℝ) := by
      have hdid : 2*delta*(D+1)=1 := by dsimp only [delta]; field_simp
      calc
        _=(2*delta*(D+1))*(L^(-20:ℝ)*L) := by ring
        _=_ := by rw [hdid,one_mul,hp]

end LipschitzHilbert

end

end OAI
