import Mathlib

namespace OAI

/-! Scalar inequalities for criticality, Poisson survival and nonlinear decay. -/

namespace ThreeState.PositiveScalar

noncomputable def lowerC (lam : ℝ) : ℝ := (37/27:ℝ)*(1+2*lam/3)

lemma small_polynomial (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 3/10) :
    (2/5-lam^2/2)*(lowerC lam)^2 > (2/3:ℝ)*(11/10+lam^2/2) := by
  have hnon : 0 ≤ (3/10:ℝ)-lam := by linarith
  have he : (2/5-lam^2/2)*(lowerC lam)^2-(2/3:ℝ)*(11/10+lam^2/2) =
    (130000/59049:ℝ)*(3/10-lam)^4+(2710400/59049:ℝ)*lam*(3/10-lam)^3+
    (6735490/59049:ℝ)*lam^2*(3/10-lam)^2+(1871120/19683:ℝ)*lam^3*(3/10-lam)+
    (159292/6561:ℝ)*lam^4 := by dsimp only [lowerC]; ring
  have hp : 0 < (130000/59049:ℝ)*(3/10-lam)^4+(2710400/59049:ℝ)*lam*(3/10-lam)^3+
    (6735490/59049:ℝ)*lam^2*(3/10-lam)^2+(1871120/19683:ℝ)*lam^3*(3/10-lam)+
    (159292/6561:ℝ)*lam^4 := by positivity
  linarith

lemma middle_polynomial (lam : ℝ) (h0 : 3/10 ≤ lam) (h1 : lam^2 ≤ 1/2) :
    1-17*lam/25 < (2/5-lam^2/2)*(lowerC lam)^2 := by
  have ha : 0 ≤ lam-(3/10:ℝ) := by linarith
  have hb : 0 < (71/100:ℝ)-lam := by nlinarith
  have he : (2/5-lam^2/2)*(lowerC lam)^2-(1-17*lam/25) =
    (1328320000/228886641:ℝ)*(71/100-lam)^4+
    (75777584000/2059979769:ℝ)*(lam-3/10)*(71/100-lam)^3+
    (1184570339800/18539817921:ℝ)*(lam-3/10)^2*(71/100-lam)^2+
    (674265198440/18539817921:ℝ)*(lam-3/10)^3*(71/100-lam)+
    (56362261022/18539817921:ℝ)*(lam-3/10)^4 := by dsimp only [lowerC]; ring
  have hp : 0 < (1328320000/228886641:ℝ)*(71/100-lam)^4+
    (75777584000/2059979769:ℝ)*(lam-3/10)*(71/100-lam)^3+
    (1184570339800/18539817921:ℝ)*(lam-3/10)^2*(71/100-lam)^2+
    (674265198440/18539817921:ℝ)*(lam-3/10)^3*(71/100-lam)+
    (56362261022/18539817921:ℝ)*(lam-3/10)^4 := by positivity
  linarith

lemma rational_lower (mu : ℝ) (hm : 0 ≤ mu) : 3/2-mu ≤ 3/(2*(1+2*mu/3)) := by
  apply (le_div_iff₀ (by positivity : 0 < 2*(1+2*mu/3))).mpr
  nlinarith [sq_nonneg mu]

lemma regular_scalar (lam mu c : ℝ) (h0 : 0 < lam) (hl : lam^2 ≤ 1/2)
    (hm : 0 ≤ mu) (hc : lowerC lam ≤ c) (hb : mu*c^2 ≤ 1) :
    8/5 < (1-lam^2)/2+3/(2*(1+2*mu/3))+17*lam*mu/25 := by
  have hl1 : lam < 1 := by nlinarith
  have hc0 : 0 < lowerC lam := by dsimp only [lowerC]; positivity
  have hc2 : (lowerC lam)^2 ≤ c^2 := sq_le_sq₀ hc0.le (hc0.trans_le hc).le |>.mpr hc
  have hcpos : 0 < c := hc0.trans_le hc
  have hden : 0 < 2*(1+2*mu/3) := by positivity
  rcases le_total lam (3/10) with hs | hs
  · have hp := small_polynomial lam h0 hs
    have hfac : 0 < 2/5-lam^2/2 := by nlinarith
    have hpc : (2/3:ℝ)*(11/10+lam^2/2) < (2/5-lam^2/2)*c^2 :=
      hp.trans_le (mul_le_mul_of_nonneg_left hc2 hfac.le)
    have ht : (11/10+lam^2/2)*mu < (3/2:ℝ)*(2/5-lam^2/2) := by
      have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ 11/10+lam^2/2 by positivity)
      have hh' := mul_lt_mul_of_pos_left hpc (show 0 < (3/2:ℝ) by norm_num)
      have he : ((11/10+lam^2/2)*mu)*c^2 < ((3/2:ℝ)*(2/5-lam^2/2))*c^2 := by nlinarith only [hh,hh']
      exact (mul_lt_mul_iff_left₀ (sq_pos_of_pos hcpos)).mp he
    have he : 11/10+lam^2/2 < 3/(2*(1+2*mu/3)) := by
      apply (lt_div_iff₀ hden).mpr
      nlinarith only [ht]
    have hlast : 0 ≤ 17*lam*mu/25 := by positivity
    linarith
  · have hpoly := middle_polynomial lam hs hl
    have hfac : 0 < 2/5-lam^2/2 := by nlinarith
    have hpc : 1-17*lam/25 < (2/5-lam^2/2)*c^2 :=
      hpoly.trans_le (mul_le_mul_of_nonneg_left hc2 hfac.le)
    have hcoef : 0 < 1-17*lam/25 := by linarith
    have hh := mul_le_mul_of_nonneg_left hb hcoef.le
    have ht : (1-17*lam/25)*mu < 2/5-lam^2/2 := by
      apply (mul_lt_mul_iff_left₀ (sq_pos_of_pos hcpos)).mp
      nlinarith only [hpc,hh]
    have hr := rational_lower mu hm
    nlinarith only [ht,hr]

lemma high_scalar (lam mu c : ℝ) (h0 : 0 < lam) (hl1 : lam < 1) (hl : 1/2 < lam^2)
    (hm : 0 ≤ mu) (hc : lowerC lam ≤ c) (hb : mu*c^2 ≤ 1) :
    8/5 < (1/4:ℝ)+3/(2*(1+2*mu/3))+17*lam*mu/25 := by
  have hx : (707/1000:ℝ) < lam := by nlinarith
  have hc' : (37/27:ℝ)*(1+2*(707/1000:ℝ)/3) < c := by dsimp only [lowerC] at hc; linarith
  have hcpos : 0 < c := by linarith
  have hp : 1-17*lam/25 < (3/20:ℝ)*c^2 := by nlinarith [sq_nonneg (c-(37/27:ℝ)*(1+2*(707/1000:ℝ)/3))]
  have hcoef : 0 < 1-17*lam/25 := by linarith
  have hh := mul_le_mul_of_nonneg_left hb hcoef.le
  have ht : (1-17*lam/25)*mu < (3/20:ℝ) := by
    apply (mul_lt_mul_iff_left₀ (sq_pos_of_pos hcpos)).mp
    nlinarith only [hp,hh]
  have hr := rational_lower mu hm
  nlinarith only [ht,hr]

 

theorem scalar_contradiction (lam mu c s : ℝ) (h0 : 0 < lam) (h1 : lam < 1)
    (hm : 0 ≤ mu) (hs0 : 0 < s) (hs1 : s ≤ 1) (hc : lowerC lam ≤ c)
    (hb : mu*c^2 ≤ s) (hsurv : 1/2 < lam^2 → s ≤ 2*(1-lam^2)) :
    8/5 < (1-lam^2)/(2*s)+3/(2*(1+2*mu/3))+17*lam*mu/(25*s) := by
  have hlast : 17*lam*mu/25 ≤ 17*lam*mu/(25*s) := by
    apply (le_div_iff₀ (by positivity : 0 < 25*s)).mpr
    nlinarith [mul_nonneg (show 0 ≤ 17*lam*mu by positivity) (show 0 ≤ 1-s by linarith)]
  rcases le_or_gt (lam^2) (1/2) with hl | hl
  · have hh := regular_scalar lam mu c h0 hl hm hc (hb.trans hs1)
    have hf : (1-lam^2)/2 ≤ (1-lam^2)/(2*s) := by
      apply (le_div_iff₀ (by positivity : 0 < 2*s)).mpr
      nlinarith [mul_nonneg (show 0 ≤ 1-lam^2 by nlinarith) (show 0 ≤ 1-s by linarith)]
    linarith
  · have hh := high_scalar lam mu c h0 h1 hl hm hc (hb.trans hs1)
    have hf : (1/4:ℝ) ≤ (1-lam^2)/(2*s) := by
      apply (le_div_iff₀ (by positivity : 0 < 2*s)).mpr
      linarith [hsurv hl]
    linarith

end ThreeState.PositiveScalar

namespace ThreeState.PositiveScalar

lemma q_lower (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    (37/81:ℝ) ≤ (37/27:ℝ)/(2+lam) := by
  apply (le_div_iff₀ (by linarith : 0 < 2+lam)).mpr
  linarith

lemma root_loss : (1:ℝ)/Real.sqrt 2 < 113/81-17/25 := by
  have hr : 0 < Real.sqrt 2 := by positivity
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply (div_lt_iff₀ hr).mpr
  nlinarith only [hs, Real.sqrt_nonneg 2]

lemma J_square_bound (lam mu nu J : ℝ) (h0 : 0 < lam) (h1 : lam < 1)
    (hm : 0 ≤ mu) (hn : 0 ≤ nu) (hJ0 : 0 ≤ J)
    (hJ : J ≤ mu-lam*((37/27:ℝ)/(2+lam))*nu)
    (hc : ((37/27:ℝ)+2*lam*((37/27:ℝ)/(2+lam)))^2*nu ≤ mu) :
    (8/5:ℝ)*J^2 ≤ (8/5:ℝ)*mu^2-(113/81:ℝ)*lam*mu*nu := by
  let q : ℝ := (37/27:ℝ)/(2+lam)
  let A := lam*q*nu
  have hq := q_lower lam h0.le h1.le
  change (37/81:ℝ) ≤ q at hq
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hAc : 8*(37/27:ℝ)*A ≤ mu := by
    have hh := mul_le_mul_of_nonneg_right (sq_nonneg ((37/27:ℝ)-2*lam*q)) hn
    dsimp only [A,q] at *
    nlinarith only [hh,hc]
  have hA : A ≤ (27/296:ℝ)*mu := by linarith only [hAc]
  have hs := mul_le_mul_of_nonneg_right hA hA0
  change J ≤ mu-A at hJ
  have hj2 : J^2 ≤ (mu-A)^2 := (sq_le_sq₀ hJ0 (hJ0.trans hJ)).mpr hJ
  have hqmu := mul_le_mul_of_nonneg_right hq (show 0 ≤ lam*mu*nu by positivity)
  have hlead : mu*A = q*(lam*mu*nu) := by dsimp only [A]; ring
  rw [← hlead] at hqmu
  nlinarith only [hj2,hs,hqmu]

lemma scalar_from_moments (lam mu nu J s : ℝ) (h0 : 0 < lam) (h1 : lam < 1)
    (hm : 0 < mu) (hn : 0 ≤ nu) (hs0 : 0 < s) (_ : s ≤ 1)
    (hsecond : mu^2 ≤ s*nu)
    (hcnu : ((37/27:ℝ)+2*lam*((37/27:ℝ)/(2+lam)))^2*nu ≤ mu)
    (hJ0 : 0 ≤ J) (hJ : J ≤ mu-lam*((37/27:ℝ)/(2+lam))*nu)
    (hentropy : (1-lam^2)/2*nu+3*mu^2/(2*(1+2*mu/3))-lam*mu*nu/Real.sqrt 2 ≤ (8/5:ℝ)*J^2) :
    8/5 ≥ (1-lam^2)/(2*s)+3/(2*(1+2*mu/3))+17*lam*mu/(25*s) := by
  have hj2 := J_square_bound lam mu nu J h0 h1 hm.le hn hJ0 hJ hcnu
  have hroot := mul_le_mul_of_nonneg_right root_loss.le (show 0 ≤ lam*mu*nu by positivity)
  have he : ((1-lam^2)/2+17*lam*mu/25)*nu+3*mu^2/(2*(1+2*mu/3)) ≤ (8/5:ℝ)*mu^2 := by
    simp only [div_eq_mul_inv] at hentropy hj2 hroot ⊢
    nlinarith only [hentropy,hj2,hroot]
  have ha : 0 ≤ (1-lam^2)/2+17*lam*mu/25 := by
    have hh : 0 ≤ 1-lam^2 := by nlinarith
    positivity
  have hh := mul_le_mul_of_nonneg_left ((div_le_iff₀ hs0).mpr (show mu^2 ≤ nu*s by nlinarith only [hsecond])) ha
  have hneed : ((1-lam^2)/(2*s)+3/(2*(1+2*mu/3))+17*lam*mu/(25*s))*mu^2 ≤ (8/5:ℝ)*mu^2 := by
    simp only [div_eq_mul_inv, mul_inv_rev] at he hh ⊢
    nlinarith only [he,hh]
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hm)).mp hneed

lemma moment_scalar_contradiction (lam mu nu J s : ℝ) (h0 : 0 < lam) (h1 : lam < 1)
    (hm : 0 < mu) (hn : 0 ≤ nu) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hsecond : mu^2 ≤ s*nu)
    (hcnu : ((37/27:ℝ)+2*lam*((37/27:ℝ)/(2+lam)))^2*nu ≤ mu)
    (hJ0 : 0 ≤ J) (hJ : J ≤ mu-lam*((37/27:ℝ)/(2+lam))*nu)
    (hentropy : (1-lam^2)/2*nu+3*mu^2/(2*(1+2*mu/3))-lam*mu*nu/Real.sqrt 2 ≤ (8/5:ℝ)*J^2)
    (hsurv : 1/2 < lam^2 → s ≤ 2*(1-lam^2)) : False := by
  let c : ℝ := (37/27:ℝ)+2*lam*((37/27:ℝ)/(2+lam))
  have hc : 0 < c := by dsimp only [c]; positivity
  have hcL : lowerC lam ≤ c := by
    have hh := q_lower lam h0.le h1.le
    dsimp only [lowerC,c]
    nlinarith only [hh,h0]
  have hb : mu*c^2 ≤ s := by
    have hh := mul_le_mul_of_nonneg_right hsecond (sq_nonneg c)
    have hh' := mul_le_mul_of_nonneg_left hcnu hs0.le
    apply (mul_le_mul_iff_left₀ hm).mp
    dsimp only [c] at *
    nlinarith only [hh,hh']
  have hfalse := scalar_contradiction lam mu c s h0 h1 hm.le hs0 hs1 hcL hb hsurv
  have hneed := scalar_from_moments lam mu nu J s h0 h1 hm hn hs0 hs1 hsecond hcnu hJ0 hJ hentropy
  linarith only [hfalse,hneed]

end ThreeState.PositiveScalar

namespace ThreeState
open Filter Topology

lemma poisson_sqrt_tangent (d lam t : ℝ) (_ : 0<d) (hl : 0<lam) (ht : 0≤t)
    (hc : d*lam^2=1) : Real.sqrt t ≤ lam*(t+d/2)/Real.sqrt 2 := by
  have hs2 : (Real.sqrt 2)^2=(2:ℝ) := Real.sq_sqrt (by norm_num)
  have hst : (Real.sqrt t)^2=t := Real.sq_sqrt ht
  have hsp : 0 < Real.sqrt (2:ℝ) := by positivity
  apply (le_div_iff₀ hsp).mpr
  apply (mul_le_mul_iff_right₀ hl).mp
  have hp := sq_nonneg (Real.sqrt 2*lam*Real.sqrt t-1)
  have he : (Real.sqrt 2*lam*Real.sqrt t)^2=2*lam^2*t := by
    calc _ = (Real.sqrt 2)^2*lam^2*(Real.sqrt t)^2 := by ring
         _ = _ := by rw [hs2,hst]
  nlinarith only [hp,he,hc]

lemma poisson_reciprocal_tangent (t beta D : ℝ) (ht : 0≤t) (hb : 0≤beta) (hD : 0<D) :
    t*(2*D-1-beta*t)/D^2 ≤ t/(1+beta*t) := by
  have hy : 0<1+beta*t := by positivity
  apply (div_le_div_iff₀ (sq_pos_of_pos hD) hy).mpr
  nlinarith only [mul_nonneg ht (sq_nonneg (D-(1+beta*t)))]

 

lemma poisson_correlation_scalar (d lam mu nu : ℝ) (hd : 0<d) (hl : 0<lam)
    (hm : 0 ≤ mu) (hn : 0≤nu) (hc : d*lam^2=1)
    (H C : ℝ → ℝ) (hH0 : H 0=0)
    (hderiv : ∀ t ∈ Set.Icc 0 d, HasDerivAt H (C t) t)
    (hlower : ∀ t ∈ Set.Icc 0 d,
      3*lam^4*mu^2*t/(1+t*lam^2*mu)-lam^4*mu*nu*Real.sqrt t ≤ 3*C t) :
    3*mu^2/(2*(1+2*mu/3))-lam*mu*nu/Real.sqrt 2 ≤ 3*H d := by
  let D := 1+2*mu/3
  have hD : 0<D := by dsimp [D]; positivity
  let P := fun t : ℝ => (3*lam^4*mu^2/D^2)*((2*D-1)*t^2/2-(lam^2*mu)*t^3/3)-
    (lam^5*mu*nu/Real.sqrt 2)*(t^2/2+d*t/2)
  let P' := fun t : ℝ => (3*lam^4*mu^2/D^2)*((2*D-1)*t-(lam^2*mu)*t^2)-
    (lam^5*mu*nu/Real.sqrt 2)*(t+d/2)
  have hp (t : ℝ) : HasDerivAt P (P' t) t := by
    have hh := (((((hasDerivAt_pow 2 t).const_mul (2*D-1)).div_const 2).sub
      (((hasDerivAt_pow 3 t).const_mul (lam^2*mu)).div_const 3)).const_mul (3*lam^4*mu^2/D^2)).sub
      ((((hasDerivAt_pow 2 t).div_const 2).add (((hasDerivAt_id t).const_mul d).div_const 2)).const_mul (lam^5*mu*nu/Real.sqrt 2))
    convert hh using 1 <;> try rfl
    dsimp only [P']
    ring
  have hpd (t : ℝ) (ht : t ∈ Set.Icc 0 d) : P' t ≤ 3*C t := by
    have hr := mul_le_mul_of_nonneg_left (poisson_reciprocal_tangent t (lam^2*mu) D ht.1 (by positivity) hD)
      (show 0≤3*lam^4*mu^2 by positivity)
    have hs := mul_le_mul_of_nonneg_left (poisson_sqrt_tangent d lam t hd hl ht.1 hc)
      (show 0≤lam^4*mu*nu by positivity)
    calc
      P' t = 3*lam^4*mu^2*(t*(2*D-1-(lam^2*mu)*t)/D^2)-lam^4*mu*nu*(lam*(t+d/2)/Real.sqrt 2) := by dsimp only [P']; ring
      _ ≤ 3*lam^4*mu^2*(t/(1+(lam^2*mu)*t))-lam^4*mu*nu*Real.sqrt t := sub_le_sub hr hs
      _ = 3*lam^4*mu^2*t/(1+t*lam^2*mu)-lam^4*mu*nu*Real.sqrt t := by ring
      _ ≤ _ := hlower t ht
  have hmono : MonotoneOn (fun t => 3*H t-P t) (Set.Icc 0 d) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 d) (f' := fun t => 3*C t-P' t)
    · intro t ht
      exact (((hderiv t ht).const_mul 3).sub (hp t)).continuousAt.continuousWithinAt
    · intro t ht
      exact (((hderiv t (interior_subset ht)).const_mul 3).sub (hp t)).hasDerivWithinAt
    · intro t ht
      exact sub_nonneg.mpr (hpd t (interior_subset ht))
  have hh := hmono (show (0:ℝ)∈Set.Icc 0 d from ⟨le_rfl,hd.le⟩) (show d∈Set.Icc 0 d from ⟨hd.le,le_rfl⟩) hd.le
  have hp0 : P 0=0 := by simp [P]
  have hpend : P d=3*mu^2/(2*D)-lam*mu*nu/Real.sqrt 2 := by
    have hd2 : d^2*lam^4=1 := by nlinarith [sq_nonneg (d*lam^2-1)]
    have hd3 : d^3*lam^6=1 := by
      calc
        _ = (d*lam^2)^3 := by ring
        _ = 1 := by rw [hc]; norm_num
    dsimp only [P]
    field_simp [ne_of_gt hD]
    dsimp only [D]
    nlinarith only [congrArg (fun x : ℝ => x*(Real.sqrt 2)*mu^2) hd2,
      congrArg (fun x : ℝ => x*(Real.sqrt 2)*mu^3) hd2,
      congrArg (fun x : ℝ => x*(Real.sqrt 2)*mu^3) hd3,
      congrArg (fun x : ℝ => x*lam*mu*nu) hd2,
      congrArg (fun x : ℝ => x*lam*mu^2*nu) hd2,
      congrArg (fun x : ℝ => x*lam*mu^3*nu) hd2]
  change 3*H 0-P 0 ≤ 3*H d-P d at hh
  rw [hH0,hp0,hpend] at hh
  dsimp only [D] at hh
  linarith

end ThreeState

namespace ThreeState
open Filter Topology

lemma log_survival_bound (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    2*s/(2-s) ≤ -Real.log (1-s) := by
  let F := fun x : ℝ => -Real.log (1-x)-2*x/(2-x)
  have hd (x : ℝ) (hx : x ∈ Set.Icc 0 s) : HasDerivAt F
      (1/(1-x)-4/(2-x)^2) x := by
    have h1 : 1-x ≠ 0 := by linarith [hx.2]
    have h2 : 2-x ≠ 0 := by linarith [hx.2]
    convert (((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).log h1).neg.sub
      (((hasDerivAt_id x).const_mul 2).div ((hasDerivAt_const x (2:ℝ)).sub (hasDerivAt_id x)) h2) using 1 <;> try rfl
    dsimp
    field_simp
    ring
  have hder (x : ℝ) (hx : x ∈ Set.Icc 0 s) : 0 ≤ 1/(1-x)-4/(2-x)^2 := by
    have h1 : 0 < 1-x := by linarith [hx.2]
    have h2 : 0 < 2-x := by linarith [hx.2]
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (sq_pos_of_pos h2) h1).mpr
    nlinarith [sq_nonneg x]
  have hmono : MonotoneOn F (Set.Icc 0 s) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 s)
      (f' := fun x => 1/(1-x)-4/(2-x)^2)
    · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx; exact (hd x (interior_subset hx)).hasDerivWithinAt
    · intro x hx; exact hder x (interior_subset hx)
  have hh := hmono (show (0:ℝ)∈Set.Icc 0 s from ⟨le_rfl,hs0⟩) (show s∈Set.Icc 0 s from ⟨hs0,le_rfl⟩) hs0
  dsimp only [F] at hh
  norm_num at hh
  linarith

lemma poisson_support_bound (d s : ℝ) (hd : 0 < d) (hs : 0 < s)
    (hfp : Real.exp (-d*s) ≤ 1-s) : s ≤ 2*(1-d⁻¹) := by
  have hs1 : s < 1 := by linarith [Real.exp_pos (-d*s)]
  have hlog := Real.log_le_log (Real.exp_pos (-d*s)) hfp
  rw [Real.log_exp] at hlog
  have hh := log_survival_bound s hs.le hs1
  have hden : 0 < 2-s := by linarith
  have hrat : 2*s/(2-s) ≤ d*s := by linarith
  have hr := (div_le_iff₀ hden).mp hrat
  have hsd : 2 ≤ d*(2-s) := (mul_le_mul_iff_right₀ hs).mp (by nlinarith only [hr])
  apply (mul_le_mul_iff_left₀ hd).mp
  have he : (2*(1-d⁻¹))*d=2*d-2 := by field_simp
  rw [he]
  nlinarith only [hsd]
end ThreeState

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical
noncomputable section

lemma bernoulli_lower (t:ℝ) (ht0:0≤t) (ht1:t≤1) (k:ℕ) : 1-k*t≤(1-t)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh:=mul_le_mul_of_nonneg_right ih (by linarith : 0≤1-t)
    rw [pow_succ (1-t) k,Nat.cast_succ]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) (mul_nonneg ht0 ht0)]

lemma bernoulli_quadratic_lower (t:ℝ) (ht0:0≤t) (ht1:t≤1) (k:ℕ) (hk:2≤k) :
    1-k*t+t^2≤(1-t)^k := by
  induction k,hk using Nat.le_induction with
  | base => norm_num;ring_nf;exact le_refl _
  | succ k hk ih =>
    have hh:=mul_le_mul_of_nonneg_right ih (by linarith : 0≤1-t)
    have hkr:(2:ℝ)≤k:=by exact_mod_cast hk
    have hp:=mul_nonneg (show 0≤(k:ℝ)-t by linarith) (show 0≤t^2 by exact pow_nonneg ht0 2)
    rw [pow_succ (1-t) k,Nat.cast_succ]
    nlinarith

 
def decaySeq (c:ℝ) : ℕ→ℝ
  | 0=>1
  | n+1=>decaySeq c n-c*(decaySeq c n)^2
lemma decaySeq_bounds (c:ℝ) (hc0:0≤c) (hc1:c≤1) (n:ℕ) :
    0≤decaySeq c n ∧ decaySeq c n≤1 := by
  induction n with
  | zero => simp [decaySeq]
  | succ n ih =>
    have hp:0≤c*(decaySeq c n)^2:=mul_nonneg hc0 (sq_nonneg _)
    have ht:c*decaySeq c n≤1:=(mul_le_mul_of_nonneg_right hc1 ih.1).trans (by simpa using ih.2)
    have hh:=mul_nonneg ih.1 (show 0≤1-c*decaySeq c n by linarith)
    simp only [decaySeq]
    constructor <;> nlinarith
lemma decaySeq_antitone (c:ℝ) (hc:0≤c) : Antitone (decaySeq c) :=
  antitone_nat_of_succ_le (fun n=>by dsimp [decaySeq];nlinarith [mul_nonneg hc (sq_nonneg (decaySeq c n))])
lemma decaySeq_tendsto (c:ℝ) (hc:0<c) (hc1:c≤1) : Tendsto (decaySeq c) atTop (𝓝 0) := by
  have hb : BddBelow (Set.range (decaySeq c)) := ⟨0,by rintro x ⟨n,rfl⟩;exact (decaySeq_bounds c hc.le hc1 n).1⟩
  have hl:=tendsto_atTop_ciInf (decaySeq_antitone c hc.le) hb
  let L:ℝ:=⨅n,decaySeq c n
  have hl':Tendsto (fun n=>decaySeq c (n+1)) atTop (𝓝 L):=hl.comp (Filter.tendsto_add_atTop_nat 1)
  have hrec:Tendsto (fun n=>decaySeq c (n+1)) atTop (𝓝 (L-c*L^2)):=hl.sub (tendsto_const_nhds.mul (hl.pow 2))
  have he:L=L-c*L^2:=tendsto_nhds_unique hl' hrec
  have hzero:c*L^2=0:=by linarith
  have hz:L=0:= (eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hzero).resolve_left hc.ne'))
  have hlast:Tendsto (decaySeq c) atTop (𝓝 L):=hl
  rwa [hz] at hlast
end
end ThreeState

end OAI
