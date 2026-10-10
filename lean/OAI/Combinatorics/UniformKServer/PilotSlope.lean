import Mathlib
import OAI.Combinatorics.UniformKServer.PilotRelocation

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]
def localSlopeConstant (σ L : ℝ) : ℝ :=
  (L+1024/σ)*(514+8/σ)+1024*(5+L)/σ^2

omit [MetricSpace X] in
theorem sum_split_single [DecidableEq X] (f : X → ℝ) (s : X) :
    (∑ t, f t) = f s+∑ t, if t=s then 0 else f t := by
  classical
  have he : ∀ t, f t = (if t=s then f s else 0)+(if t=s then 0 else f t) := by
    intro t
    split_ifs with ht <;> simp_all
  calc
    _ = ∑ t, ((if t=s then f s else 0)+(if t=s then 0 else f t)) :=
      Finset.sum_congr rfl (fun t _ => he t)
    _ = _ := by rw [Finset.sum_add_distrib]; simp

theorem capacity_other [DecidableEq X] (r σ R : ℝ) (hR : 0<R) (z : X → ℝ)
    (hz : feasible r σ R z) (s x : X) (hs : dist s x/r ≤ 10*R)
    (P : X → Prop) [DecidablePred P] (hP : ∀ t, P t → dist t x/r ≤ 10*R) :
    (∑ t, if t=s then 0 else if P t then z t else 0) ≤ 1-z s := by
  classical
  have hcap := hz.2.1 x
  rw [sum_split_single _ s, gate_eq_zero R _ hR hs, sub_zero, max_eq_left (hz.1 s)] at hcap
  have hh : (∑ t, if t=s then 0 else if P t then z t else 0) ≤
      ∑ t, if t=s then 0 else max (z t-gate R (dist t x/r)) 0 := by
    apply Finset.sum_le_sum
    intro t ht
    by_cases he : t=s
    · simp [he]
    · rw [ite_eq_right he,ite_eq_right he]
      by_cases hp : P t
      · rw [ite_eq_left hp,gate_eq_zero R _ hR (hP t hp),sub_zero,max_eq_left (hz.1 t)]
      · rw [ite_eq_right hp]
        exact le_max_right _ _
  linarith

theorem local_bump_sum (r σ R : ℝ) (hr : 0<r) (hσ : 0<σ) (hσ1 : σ≤1) (hR : 256≤R)
    (z : X → ℝ) (hz : feasible r σ R z) (s x p : X) (hnear : dist s x/r < σ/4)
    (hother : ∀ t, t≠s → 0<z t → R/2<dist t x/r) (hp : dist x p/r < σ/8) :
    (∑ t, z t*bumpB σ (dist t p/r)) = z s := by
  classical
  rw [Finset.sum_eq_single s]
  · have hh := normalized_triangle r hr s x p
    rw [bumpB_one σ _ hσ (by linarith),mul_one]
  · intro t ht hts
    rcases (hz.1 t).eq_or_lt with he | htpos
    · rw [←he,zero_mul]
    · have hfar := hother t hts htpos
      have hh := normalized_triangle r hr t p x
      rw [dist_comm p x] at hh
      rw [bumpB_zero σ _ hσ (by linarith),mul_zero]
  · simp

theorem other_surcharge_slope [DecidableEq X] (r σ R : ℝ) (hr : 0<r) (hσ : 0<σ)
    (hσ1 : σ≤1) (hR : 256≤R) (g z : X → ℝ) (hg : ∀ p,g p∈Set.Icc (0:ℝ) 1)
    (hz : feasible r σ R z) (s x y : X)
    (hnear : dist s x/r < σ/4) (hxy : dist x y/r < σ/8) :
    (∑ t, if t=s then 0 else z t*(1+g t)*(bumpA σ R (dist t x/r)-bumpA σ R (dist t y/r))) ≤
      (4/σ)*(1-z s)*(dist x y/r) := by
  classical
  let P : X → Prop := fun t => bumpA σ R (dist t x/r)≠0 ∨ bumpA σ R (dist t y/r)≠0
  let W : X → ℝ := fun t => if t=s then 0 else if P t then z t else 0
  have hRpos : 0<R := by linarith
  have hv : 0≤dist x y/r := by positivity
  have hP : ∀ t, P t → dist t x/r≤10*R := by
    intro t ht
    have hn : ∀ q, bumpA σ R (dist t q/r)≠0 → dist t q/r<2*R := by
      intro q ha
      by_contra hh
      exact ha (bumpA_zero σ R _ hRpos (le_of_not_gt hh))
    rcases ht with hx | hy
    · linarith [hn x hx]
    · have hh := normalized_triangle r hr t y x
      rw [dist_comm y x] at hh
      linarith [hn y hy]
  have hW : (∑ t, W t)≤1-z s := capacity_other r σ R hRpos z hz s x (by linarith) P hP
  have hterm : ∀ t, (if t=s then 0 else z t*(1+g t)*(bumpA σ R (dist t x/r)-bumpA σ R (dist t y/r))) ≤
      ((4/σ)*(dist x y/r))*W t := by
    intro t
    by_cases hts : t=s
    · simp [W,hts]
    rw [ite_eq_right hts]
    by_cases hp : P t
    · dsimp [W]
      rw [ite_eq_right hts,ite_eq_left hp]
      have hd : |dist t x/r-dist t y/r| ≤ dist x y/r := by
        simpa only [dist_comm t x,dist_comm t y] using normalized_dist_difference r hr x y t
      have ha := (bumpA_lipschitz σ R _ _ hσ hσ1 hR (by positivity) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hd (by positivity : 0≤2/σ))
      have hg0 : 0≤1+g t := by linarith [(hg t).1]
      have hg2 : 1+g t≤2 := by linarith [(hg t).2]
      calc
        _ ≤ z t*(1+g t)*|bumpA σ R (dist t x/r)-bumpA σ R (dist t y/r)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg (hz.1 t) hg0)
        _ ≤ z t*2*((2/σ)*(dist x y/r)) := mul_le_mul
          (mul_le_mul_of_nonneg_left hg2 (hz.1 t)) ha (abs_nonneg _) (mul_nonneg (hz.1 t) (by norm_num))
        _ = _ := by ring
    · have hx : bumpA σ R (dist t x/r)=0 := by by_contra hh; exact hp (Or.inl hh)
      have hy : bumpA σ R (dist t y/r)=0 := by by_contra hh; exact hp (Or.inr hh)
      simp [W,hts,hp,hx,hy]
  calc
    _ ≤ ∑ t, ((4/σ)*(dist x y/r))*W t := Finset.sum_le_sum fun t _ => hterm t
    _ = ((4/σ)*(dist x y/r))*(∑ t,W t) := (Finset.mul_sum _ _ _).symm
    _ ≤ ((4/σ)*(dist x y/r))*(1-z s) := mul_le_mul_of_nonneg_left hW (by positivity)
    _ = _ := by ring

theorem square_difference (u w v : ℝ) (hu : 0≤u) (hw : 0≤w) (hv : 0≤v)
    (hd : w-u≤v) : w^2-u^2≤2*w*v := by
  by_cases hup : u≤w
  · have h1 := mul_nonneg (show 0≤w+u by linarith) (show 0≤v-(w-u) by linarith)
    have h2 := mul_nonneg (show 0≤w-u by linarith) hv
    nlinarith only [h1,h2]
  · nlinarith [mul_nonneg hw hv]

theorem near_surcharge_slope (r σ R : ℝ) (hr : 0<r) (hσ : 0<σ)
    (hσ1 : σ≤1) (hR : 256≤R) (g z : X → ℝ) (hg : ∀ p,g p∈Set.Icc (0:ℝ) 1)
    (hz : feasible r σ R z) (s x y : X)
    (hnear : dist s x/r < σ/4) (hxy : dist x y/r < σ/8) :
    256*z s*(1+g s)*(bumpA σ R (dist s x/r)-bumpA σ R (dist s y/r)) ≤
      (1024*(dist s x/r)/σ^2)*(dist x y/r) := by
  let w := dist s x/r
  let u := dist s y/r
  let v := dist x y/r
  have hw : 0≤w := by dsimp [w]; positivity
  have hu : 0≤u := by dsimp [u]; positivity
  have hv : 0≤v := by dsimp [v]; positivity
  have htri := normalized_triangle r hr s x y
  have htri' := normalized_triangle r hr s y x
  rw [dist_comm y x] at htri'
  have huσ : u≤σ := by dsimp [u]; linarith
  have hwσ : w≤σ := by dsimp [w]; linarith
  have hd := square_difference u w v hu hw hv (by dsimp [u,w,v]; linarith)
  have hgain : w^2/σ^2-u^2/σ^2≤2*w*v/σ^2 := by
    rw [←sub_div]
    exact div_le_div_of_nonneg_right hd (sq_nonneg σ)
  have hzs : z s≤1 := feasible_upper r σ R z hz s
  have hg0 : 0≤1+g s := by linarith [(hg s).1]
  have hg2 : 1+g s≤2 := by linarith [(hg s).2]
  change 256*z s*(1+g s)*(bumpA σ R w-bumpA σ R u) ≤ _
  rw [bumpA_quadratic σ R w hσ (by linarith) hw hwσ,bumpA_quadratic σ R u hσ (by linarith) hu huσ]
  calc
    _ ≤ 256*z s*(1+g s)*(2*w*v/σ^2) := mul_le_mul_of_nonneg_left hgain (mul_nonneg (mul_nonneg (by norm_num) (hz.1 s)) hg0)
    _ ≤ 512*(2*w*v/σ^2) := mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg (hz.1 s) (sub_nonneg.mpr hg2)]) (by positivity)
    _ = _ := by dsimp [w,v]; ring

theorem local_slope_raw (r σ R L : ℝ) (hr : 0<r) (hσ : 0<σ)
    (hσ1 : σ≤1) (hR : 256≤R) (_hL : 0≤L)
    (g z : X → ℝ) (hg : ∀ p,g p∈Set.Icc (0:ℝ) 1)
    (hgLip : ∀ p q, |g p-g q|≤L*(dist p q/r))
    (hz : feasible r σ R z) (s x y : X)
    (hnear : dist s x/r<σ/4) (hother : ∀ t,t≠s → 0<z t → R/2<dist t x/r)
    (hxy : dist x y/r<σ/8) :
    integrand r σ R g z x-integrand r σ R g z y ≤
      ((L+1024/σ)*(1-z s)+1024*(dist s x/r)/σ^2)*(dist x y/r) := by
  classical
  have hb1 := local_bump_sum r σ R hr hσ hσ1 hR z hz s x x hnear hother (by simp; positivity)
  have hb2 := local_bump_sum r σ R hr hσ hσ1 hR z hz s x y hnear hother hxy
  have hs := other_surcharge_slope r σ R hr hσ hσ1 hR g z hg hz s x y hnear hxy
  have hn := near_surcharge_slope r σ R hr hσ hσ1 hR g z hg hz s x y hnear hxy
  have hz1 : 0≤1-z s := sub_nonneg.mpr (feasible_upper r σ R z hz s)
  have hres : (1-z s)*(g x-g y)≤(1-z s)*(L*(dist x y/r)) :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hgLip x y)) hz1
  have hsum : (∑ t,z t*(1+g t)*bumpA σ R (dist t x/r)) -
      (∑ t,z t*(1+g t)*bumpA σ R (dist t y/r)) =
      z s*(1+g s)*(bumpA σ R (dist s x/r)-bumpA σ R (dist s y/r))+
      ∑ t,if t=s then 0 else z t*(1+g t)*(bumpA σ R (dist t x/r)-bumpA σ R (dist t y/r)) := by
    rw [←Finset.sum_sub_distrib]
    simp_rw [←mul_sub]
    exact sum_split_single _ s
  unfold integrand
  rw [hb1,hb2]
  ring_nf at hres hs hn hsum ⊢
  linarith only [hres,hs,hn,hsum]

theorem local_slope [DecidableEq X] (r σ R γ δ L : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hL : 0 ≤ L) (hγ : 0 < γ) (hγσ : γ ≤ σ/64) (hγL : γ ≤ 1/(1+L))
    (hδ : 0 < δ) (hδbound : δ ≤ 1/4112)
    (μ g z : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ p q, |g p-g q| ≤ L*(dist p q/r))
    (x y : X) (hM : 0 < ballMass r γ μ x)
    (hconc : ballMass r (100*R) μ x ≤ (1+δ)*ballMass r γ μ x)
    (hz : feasible r σ R z) (hmin : objective r σ R μ g z = value r σ R μ g)
    (hxy : dist x y/r < σ/8) :
    max (integrand r σ R g z x-integrand r σ R g z y) 0 ≤
      localSlopeConstant σ L *
      ((ballMass r (100*R) μ x-ballMass r γ μ x)/ballMass r γ μ x +
        innerMoment r γ μ x/ballMass r γ μ x)*(dist x y/r) := by
  obtain ⟨s,hnear,hlarge,huniq,hdef⟩ := near_site_exists r σ R γ δ hr hσ hσ1 hR hγ hγσ hδ hδbound
    μ g z hμ hg x hM hconc hz hmin
  have hs : 0<z s := by linarith
  have hdisp := near_displacement r σ R γ δ L hr hσ hσ1 hR hL hγ hγσ hγL hδ hδbound
    μ g z hμ hg hgLip x hM hconc hz hmin s hs hnear
  have hother : ∀ t,t≠s → 0<z t → R/2<dist t x/r := by
    intro t hts htp
    by_contra hf
    have hn : σ/4≤dist t x/r := by
      by_contra hh
      exact hts (huniq t htp (lt_of_not_ge hh))
    have he := middle_site_zero r σ R γ δ hr hσ hσ1 hR hγ hγσ hδ hδbound
      μ g z hμ hg x hM hconc hz hmin t hn (le_of_not_gt hf)
    linarith
  let h := (ballMass r (100*R) μ x-ballMass r γ μ x)/ballMass r γ μ x
  let t := innerMoment r γ μ x/ballMass r γ μ x
  have hh : 0≤h := div_nonneg (sub_nonneg.mpr (ballMass_mono r γ (100*R) hr.le (by linarith) μ hμ x)) hM.le
  have ht : 0≤t := div_nonneg (innerMoment_bounds r γ hr μ hμ x).1 hM.le
  have hc : 512*γ/σ^2≤8/σ := by
    calc
      _ ≤ (8*σ)/σ^2 := div_le_div_of_nonneg_right (by linarith) (sq_nonneg σ)
      _ = _ := by field_simp
  have hdef' : 1-z s≤(514+8/σ)*(h+t) := by
    have hc' := mul_le_mul_of_nonneg_right hc ht
    have hp1 : 0≤(8/σ)*h := by positivity
    change 1-z s≤(512*γ/σ^2)*t+514*h at hdef
    nlinarith only [hdef,hc',hp1,ht]
  have hv : 0≤dist x y/r := by positivity
  have hcp : 0≤L+1024/σ := by positivity
  have hsp : 0≤1024/σ^2 := by positivity
  have hk : 0≤localSlopeConstant σ L := by unfold localSlopeConstant; positivity
  refine max_le ?_ (mul_nonneg (mul_nonneg hk (add_nonneg hh ht)) hv)
  have hraw := local_slope_raw r σ R L hr hσ hσ1 hR hL g z hg hgLip hz s x y hnear hother hxy
  have h1 := mul_le_mul_of_nonneg_left hdef' hcp
  have h2 := mul_le_mul_of_nonneg_left hdisp hsp
  have hco : (L+1024/σ)*(1-z s)+1024*(dist s x/r)/σ^2 ≤ localSlopeConstant σ L*(h+t) := by
    change (1024/σ^2)*(dist s x/r) ≤ (1024/σ^2)*((5+L)*(h+t)) at h2
    calc
      _ = (L+1024/σ)*(1-z s)+(1024/σ^2)*(dist s x/r) := by ring
      _ ≤ (L+1024/σ)*((514+8/σ)*(h+t))+(1024/σ^2)*((5+L)*(h+t)) := add_le_add h1 h2
      _ = _ := by unfold localSlopeConstant; ring
  exact hraw.trans (mul_le_mul_of_nonneg_right hco hv)

end
end UniformKServer.PilotCompact


end OAI
