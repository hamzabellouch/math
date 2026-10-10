import Mathlib
import OAI.Combinatorics.UniformKServer.PilotCapacity

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]
omit [Fintype X] in
theorem coefficient_move (r σ R L : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hL : 0 ≤ L)
    (g : X → ℝ) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ p q, |g p-g q| ≤ L*(dist p q/r)) (s x p : X) :
    coefficient r σ R g x p-coefficient r σ R g s p ≤
      (1026/σ+256*L)*(dist s x/r) := by
  have hRpos : 0 < R := by linarith
  let w := dist s x/r
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hd := normalized_dist_difference r hr s x p
  have hB : |bumpB σ (dist s p/r)-bumpB σ (dist x p/r)| ≤ w/σ :=
    (bumpB_lipschitz σ _ _ hσ).trans (div_le_div_of_nonneg_right hd hσ.le)
  have hA : |bumpA σ R (dist s p/r)-bumpA σ R (dist x p/r)| ≤ (2/σ)*w :=
    (bumpA_lipschitz σ R _ _ hσ hσ1 hR (by positivity) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hd (by positivity))
  have hgdiff : |g x-g s| ≤ L*w := by
    simpa only [abs_sub_comm] using hgLip s x
  have haBounds := bumpA_bounds σ R (dist x p/r) hRpos
  have hsBounds := hg s
  have hpBounds := hg p
  have hprod : |(1+g x)*bumpA σ R (dist x p/r)-(1+g s)*bumpA σ R (dist s p/r)| ≤
      (4/σ+L)*w := by
    have he : (1+g x)*bumpA σ R (dist x p/r)-(1+g s)*bumpA σ R (dist s p/r) =
        (1+g s)*(bumpA σ R (dist x p/r)-bumpA σ R (dist s p/r))+
        (g x-g s)*bumpA σ R (dist x p/r) := by ring
    rw [he]
    calc
      _ ≤ |(1+g s)*(bumpA σ R (dist x p/r)-bumpA σ R (dist s p/r))|+
        |(g x-g s)*bumpA σ R (dist x p/r)| := abs_add_le _ _
      _ = (1+g s)*|bumpA σ R (dist s p/r)-bumpA σ R (dist x p/r)|+
        |g x-g s| *bumpA σ R (dist x p/r) := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hsBounds.1] : 0≤1+g s),
            abs_of_nonneg haBounds.1, abs_sub_comm (bumpA σ R (dist x p/r))]
      _ ≤ 2*((2/σ)*w)+(L*w)*1 := add_le_add
        (mul_le_mul (by linarith [hsBounds.2]) hA (abs_nonneg _) (by norm_num))
        (mul_le_mul hgdiff haBounds.2 haBounds.1 (mul_nonneg hL hw))
      _ = _ := by ring
  have hBg : (1+g p)*(bumpB σ (dist s p/r)-bumpB σ (dist x p/r)) ≤ 2*(w/σ) := by
    calc
      _ ≤ (1+g p)*|bumpB σ (dist s p/r)-bumpB σ (dist x p/r)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith [hpBounds.1])
      _ ≤ 2*(w/σ) := mul_le_mul (by linarith [hpBounds.2]) hB (abs_nonneg _) (by norm_num)
  have hAp : (1+g x)*bumpA σ R (dist x p/r)-(1+g s)*bumpA σ R (dist s p/r) ≤
      (4/σ+L)*w := (le_abs_self _).trans hprod
  unfold coefficient
  calc
    _ = 256*((1+g x)*bumpA σ R (dist x p/r)-(1+g s)*bumpA σ R (dist s p/r))+
        (1+g p)*(bumpB σ (dist s p/r)-bumpB σ (dist x p/r)) := by ring
    _ ≤ 256*((4/σ+L)*w)+2*(w/σ) := add_le_add (by linarith) hBg
    _ = _ := by dsimp [w]; ring

theorem relocation_pointwise_loss [DecidableEq X] (r σ R L : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hL : 0 ≤ L)
    (g z : X → ℝ) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ p q, |g p-g q| ≤ L*(dist p q/r)) (hz : feasible r σ R z)
    (s x p : X) (hsx : s ≠ x) (hzx : z x=0) :
    integrand r σ R g (relocate r R z s x) p-integrand r σ R g z p ≤
      (z s*(1026/σ+256*L)+2/(10*R))*(dist s x/r) := by
  rw [integrand_relocate r σ R g z s x p hsx hzx]
  calc
    _ ≤ z s*((1026/σ+256*L)*(dist s x/r))+2*((dist s x/r)/(10*R)) := add_le_add
      (mul_le_mul_of_nonneg_left (coefficient_move r σ R L hr hσ hσ1 hR hL g hg hgLip s x p) (hz.1 s))
      (other_reduction_loss r σ R hr hσ hR g z hg hz s x p)
    _ = _ := by ring

theorem bumpA_quadratic (σ R u : ℝ) (hσ : 0 < σ) (hσR : σ ≤ R)
    (hu : 0 ≤ u) (huσ : u ≤ σ) : bumpA σ R u = u^2/σ^2 := by
  unfold bumpA
  rw [ite_eq_left (huσ.trans hσR)]
  apply min_eq_left
  apply (div_le_iff₀ (sq_pos_of_pos hσ)).mpr
  nlinarith

theorem quadratic_gain (gs gx u v w L : ℝ)
    (hgs : gs ∈ Set.Icc (0:ℝ) 1) (hLip : gx-gs ≤ L*w)
    (_hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (htri : w ≤ u+v) (htri' : v ≤ u+w) (hLv : L*v ≤ 1) :
    w^2-5*w*v ≤ (1+gs)*u^2-(1+gx)*v^2 := by
  have hsq : (w-v)^2 ≤ u^2 := by
    have hh := mul_nonneg (show 0≤u-w+v by linarith) (show 0≤u+w-v by linarith)
    nlinarith only [hh]
  have hh1 := mul_nonneg (show 0≤1+gs by linarith [hgs.1]) (sub_nonneg.mpr hsq)
  have hh2 := mul_nonneg (show 0≤L*w-(gx-gs) by linarith) (sq_nonneg v)
  have hh3 := mul_nonneg hgs.1 (sq_nonneg w)
  have hh4 := mul_nonneg (show 0≤1-gs by linarith [hgs.2]) (mul_nonneg hw hv)
  have hh5 := mul_nonneg (show 0≤1-L*v by linarith) (mul_nonneg hw hv)
  nlinarith only [hh1,hh2,hh3,hh4,hh5]

theorem other_inner_zero (r σ R γ : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hγσ : γ ≤ σ/64)
    (z : X → ℝ) (_hz : feasible r σ R z) (s x p t : X)
    (hother : ∀ t, t ≠ s → 0 < z t → R/2 < dist t x/r)
    (hinner : dist x p ≤ γ*r) (hts : t ≠ s) (htpos : 0 < z t) :
    bumpB σ (dist t p/r) = 0 := by
  have hv : dist x p/r ≤ γ := (div_le_iff₀ hr).mpr hinner
  have ht := hother t hts htpos
  have htri := normalized_triangle r hr t p x
  rw [dist_comm p x] at htri
  apply bumpB_zero σ _ hσ
  linarith

theorem other_inner_nonpos [DecidableEq X] (r σ R γ : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hγσ : γ ≤ σ/64)
    (g z : X → ℝ) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1) (hz : feasible r σ R z)
    (s x p : X) (hother : ∀ t, t ≠ s → 0 < z t → R/2 < dist t x/r)
    (hinner : dist x p ≤ γ*r) :
    (∑ t, if t=s ∨ t=x then 0 else
      (relocate r R z s x t-z t)*coefficient r σ R g t p) ≤ 0 := by
  have hRpos : 0 < R := by linarith
  apply Finset.sum_nonpos
  intro t ht
  split_ifs with hts
  · rfl
  · have hts' : t ≠ s := fun h => hts (Or.inl h)
    have htx : t ≠ x := fun h => hts (Or.inr h)
    have hle := relocate_other_le r R hr hRpos z hz.1 s x t htx
    by_cases hpos : 0 < z t
    · have hB := other_inner_zero r σ R γ hr hσ hσ1 hR hγσ z hz s x p t hother hinner hts' hpos
      have hc : 0 ≤ coefficient r σ R g t p := by
        unfold coefficient
        rw [hB, mul_zero, sub_zero]
        exact mul_nonneg (mul_nonneg (by norm_num) (by linarith [(hg t).1]))
          (bumpA_bounds σ R _ hRpos).1
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hle) hc
    · have he : z t=0 := le_antisymm (le_of_not_gt hpos) (hz.1 t)
      have he' : relocate r R z s x t=0 := le_antisymm (he ▸ hle) (relocate_nonneg r R z hz.1 s x t)
      simp [he,he']

theorem relocated_inner_gain [DecidableEq X] (r σ R γ L : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hL : 0 ≤ L) (hγσ : γ ≤ σ/64) (hLγ : L*γ ≤ 1)
    (g z : X → ℝ) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ p q, |g p-g q| ≤ L*(dist p q/r)) (hz : feasible r σ R z)
    (s x p : X) (hsx : s ≠ x) (hzx : z x=0) (hnear : dist s x/r < σ/4)
    (hother : ∀ t, t ≠ s → 0 < z t → R/2 < dist t x/r)
    (hinner : dist x p ≤ γ*r) :
    integrand r σ R g (relocate r R z s x) p-integrand r σ R g z p ≤
      -(256*z s/σ^2)*((dist s x/r)^2-5*(dist s x/r)*(dist x p/r)) := by
  let u := dist s p/r
  let v := dist x p/r
  let w := dist s x/r
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hvγ : v ≤ γ := (div_le_iff₀ hr).mpr hinner
  have htv := normalized_triangle r hr s x p
  have hus : u ≤ σ := by dsimp [u] at *; linarith
  have hvs : v ≤ σ := by linarith
  have hb1 := bumpB_one σ u hσ hus
  have hb2 := bumpB_one σ v hσ hvs
  have ha1 := bumpA_quadratic σ R u hσ (by linarith) hu hus
  have ha2 := bumpA_quadratic σ R v hσ (by linarith) hv hvs
  have hlip : g x-g s ≤ L*w := by
    exact (le_abs_self _).trans (by simpa only [abs_sub_comm] using hgLip s x)
  have ht1 : w ≤ u+v := by
    have hh := normalized_triangle r hr s p x
    simpa only [dist_comm p x] using hh
  have ht2 : v ≤ u+w := by
    have hh := normalized_triangle r hr x s p
    rw [dist_comm x s] at hh
    dsimp [u,v,w]
    linarith
  have hLv : L*v ≤ 1 := (mul_le_mul_of_nonneg_left hvγ hL).trans hLγ
  have hquad := quadratic_gain (g s) (g x) u v w L (hg s) hlip hu hv hw ht1 ht2 hLv
  have hc : coefficient r σ R g x p-coefficient r σ R g s p ≤
      -(256/σ^2)*(w^2-5*w*v) := by
    change 256*(1+g x)*bumpA σ R v-(1+g p)*bumpB σ v -
      (256*(1+g s)*bumpA σ R u-(1+g p)*bumpB σ u) ≤ _
    rw [hb1,hb2,ha1,ha2]
    have hm := mul_le_mul_of_nonneg_left hquad (show 0≤256/σ^2 by positivity)
    calc
      _ = -(256/σ^2)*((1+g s)*u^2-(1+g x)*v^2) := by ring
      _ ≤ _ := by linarith
  rw [integrand_relocate r σ R g z s x p hsx hzx]
  have ho := other_inner_nonpos r σ R γ hr hσ hσ1 hR hγσ g z hg hz s x p hother hinner
  calc
    _ ≤ z s*(-(256/σ^2)*(w^2-5*w*v))+0 :=
      add_le_add (mul_le_mul_of_nonneg_left hc (hz.1 s)) ho
    _ = _ := by dsimp [w,v]; ring

omit [Fintype X] in
theorem coefficient_far (r σ R : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (g : X → ℝ) (t p : X) (hfar : 2*R ≤ dist t p/r) : coefficient r σ R g t p = 0 := by
  have hRpos : 0<R := by linarith
  unfold coefficient
  rw [bumpA_zero σ R _ hRpos hfar, bumpB_zero σ _ hσ (by linarith)]
  ring

theorem relocate_unchanged_outside [DecidableEq X] (r σ R : ℝ) (hr : 0<r)
    (hσ : 0<σ) (hσ1 : σ≤1) (hR : 256≤R)
    (g z : X → ℝ) (s x p : X) (hsx : s≠x) (hzx : z x=0)
    (hnear : dist s x/r < σ/4) (hfar : (100*R)*r < dist x p) :
    integrand r σ R g (relocate r R z s x) p-integrand r σ R g z p = 0 := by
  have hxp : 100*R < dist x p/r := (lt_div_iff₀ hr).mpr hfar
  have hzero : ∀ t, dist t x/r ≤ 50*R → coefficient r σ R g t p=0 := by
    intro t ht
    have hh := normalized_triangle r hr x t p
    rw [dist_comm x t] at hh
    exact coefficient_far r σ R hσ hσ1 hR g t p (by linarith)
  have hs0 := hzero s (by linarith)
  have hx0 := coefficient_far r σ R hσ hσ1 hR g x p (by linarith)
  rw [integrand_relocate r σ R g z s x p hsx hzx, hs0, hx0]
  simp only [sub_self, mul_zero, zero_add]
  apply Finset.sum_eq_zero
  intro t ht
  split_ifs with htsx
  · rfl
  · have hts : t≠s := fun h => htsx (Or.inl h)
    have htx : t≠x := fun h => htsx (Or.inr h)
    by_cases hc : dist t x ≤ (50*R)*r
    · rw [hzero t ((div_le_iff₀ hr).mpr hc), mul_zero]
    · simp [relocate, htx, hts, hc]

theorem ballMass_mono (r a b : ℝ) (hr : 0 ≤ r) (hab : a ≤ b)
    (μ : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (x : X) : ballMass r a μ x ≤ ballMass r b μ x := by
  unfold ballMass
  apply Finset.sum_le_sum
  intro p hp
  have hi : dist x p ≤ a*r → dist x p ≤ b*r := fun h => h.trans (mul_le_mul_of_nonneg_right hab hr)
  split_ifs <;> first | linarith [hμ p] | exact False.elim (by aesop)

theorem relocation_integral_loss [DecidableEq X] (r σ R γ L : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hL : 0 ≤ L) (hγσ : γ ≤ σ/64) (hLγ : L*γ ≤ 1)
    (μ g z : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ p q, |g p-g q| ≤ L*(dist p q/r)) (hz : feasible r σ R z)
    (s x : X) (hsx : s ≠ x) (hzx : z x=0) (hnear : dist s x/r < σ/4)
    (hother : ∀ t, t ≠ s → 0 < z t → R/2 < dist t x/r) :
    (∑ p, μ p*(integrand r σ R g (relocate r R z s x) p-integrand r σ R g z p)) ≤
      -(256*z s/σ^2)*((dist s x/r)^2*ballMass r γ μ x -
        5*(dist s x/r)*innerMoment r γ μ x) +
      (z s*(1026/σ+256*L)+2/(10*R))*(dist s x/r)*
        (ballMass r (100*R) μ x-ballMass r γ μ x) := by
  let A := 256*z s/σ^2
  let B := (z s*(1026/σ+256*L)+2/(10*R))*(dist s x/r)
  let w := dist s x/r
  have hbound : ∀ p, integrand r σ R g (relocate r R z s x) p-integrand r σ R g z p ≤
      -A*(w^2-5*w*(dist x p/r))*(if dist x p ≤ γ*r then 1 else 0) +
      B*((if dist x p ≤ (100*R)*r then 1 else 0)-(if dist x p ≤ γ*r then 1 else 0)) := by
    intro p
    by_cases hi : dist x p ≤ γ*r
    · have ho : dist x p ≤ (100*R)*r := hi.trans
        (mul_le_mul_of_nonneg_right (by linarith : γ ≤ 100*R) hr.le)
      simp only [ite_eq_left hi,ite_eq_left ho,sub_self,mul_zero,add_zero,mul_one]
      exact relocated_inner_gain r σ R γ L hr hσ hσ1 hR hL hγσ hLγ g z hg hgLip hz s x p hsx hzx hnear hother hi
    · rw [ite_eq_right hi]
      simp only [mul_zero,sub_zero,zero_add]
      by_cases ho : dist x p ≤ (100*R)*r
      · rw [ite_eq_left ho,mul_one]
        exact relocation_pointwise_loss r σ R L hr hσ hσ1 hR hL g z hg hgLip hz s x p hsx hzx
      · rw [ite_eq_right ho,mul_zero,relocate_unchanged_outside r σ R hr hσ hσ1 hR g z s x p hsx hzx hnear (lt_of_not_ge ho)]
  have he : (∑ p, μ p*(-A*(w^2-5*w*(dist x p/r))*(if dist x p ≤ γ*r then 1 else 0) +
      B*((if dist x p ≤ (100*R)*r then 1 else 0)-(if dist x p ≤ γ*r then 1 else 0)))) =
      -A*(w^2*ballMass r γ μ x-5*w*innerMoment r γ μ x)+B*(ballMass r (100*R) μ x-ballMass r γ μ x) := by
    unfold ballMass innerMoment
    simp only [mul_sub,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    split_ifs <;> ring
  exact (Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left (hbound p) (hμ p))).trans_eq he

theorem relocation_constant_bound (σ R L z : ℝ) (hσ : 0<σ) (hσ1 : σ≤1)
    (hR : 256≤R) (hL : 0≤L) (hz : (1:ℝ)/2≤z) :
    z*(1026/σ+256*L)+2/(10*R) ≤ (256*z/σ^2)*(5+L) := by
  have hσsq : 0<σ^2 := sq_pos_of_pos hσ
  have hz0 : 0≤z := by linarith
  have hRpos : 0<10*R := by linarith
  have hσsq1 : σ^2≤1 := by nlinarith
  have hLsq : L*σ^2≤L := by nlinarith [mul_nonneg hL (sub_nonneg.mpr hσsq1)]
  have hlin : z*(1026*σ+256*L*σ^2) ≤ z*(1026+256*L) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hz0
  have hrat : 2/(10*R)≤1 := (div_le_iff₀ hRpos).mpr (by linarith)
  have hrat0 : 0≤2/(10*R) := by positivity
  have hrat' : (2/(10*R))*σ^2≤1 :=
    (mul_le_mul_of_nonneg_left hσsq1 hrat0).trans (by simpa using hrat)
  have he : (z*(1026/σ+256*L)+2/(10*R))*σ^2 =
      z*(1026*σ+256*L*σ^2)+(2/(10*R))*σ^2 := by
    field_simp
  apply (mul_le_mul_iff_left₀ hσsq).mp
  rw [he]
  have he' : (256*z/σ^2)*(5+L)*σ^2 = 256*z*(5+L) := by field_simp
  rw [he']
  nlinarith only [hlin,hrat',hz]

theorem near_displacement [DecidableEq X] (r σ R γ δ L : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hL : 0 ≤ L) (hγ : 0 < γ) (hγσ : γ ≤ σ/64) (hγL : γ ≤ 1/(1+L))
    (hδ : 0 < δ) (hδbound : δ ≤ 1/4112)
    (μ g z : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ p q, |g p-g q| ≤ L*(dist p q/r))
    (x : X) (hM : 0 < ballMass r γ μ x)
    (hconc : ballMass r (100*R) μ x ≤ (1+δ)*ballMass r γ μ x)
    (hz : feasible r σ R z)
    (hmin : objective r σ R μ g z = value r σ R μ g)
    (s : X) (hs : 0 < z s) (hnear : dist s x/r < σ/4) :
    dist s x/r ≤ (5+L)*((ballMass r (100*R) μ x-ballMass r γ μ x)/ballMass r γ μ x +
      innerMoment r γ μ x/ballMass r γ μ x) := by
  let M := ballMass r γ μ x
  let S := ballMass r (100*R) μ x
  let T := innerMoment r γ μ x
  let w := dist s x/r
  let A := 256*z s/σ^2
  let B := z s*(1026/σ+256*L)+2/(10*R)
  have hT : 0 ≤ T := (innerMoment_bounds r γ hr μ hμ x).1
  have hSM : 0 ≤ S-M := sub_nonneg.mpr
    (ballMass_mono r γ (100*R) hr.le (by linarith) μ hμ x)
  have hC : 0 ≤ 5+L := by linarith
  by_cases hsx : s=x
  · subst s
    simp only [dist_self,zero_div]
    exact mul_nonneg hC (add_nonneg (div_nonneg hSM hM.le) (div_nonneg hT hM.le))
  have hw : 0 < w := div_pos (dist_pos.mpr hsx) hr
  have hA : 0 < A := by dsimp [A]; positivity
  have hlarge : (3:ℝ)/4 ≤ z s := by
    have hh := nearWeight_large r σ R γ δ hr hσ hσ1 hR hγ hγσ hδ hδbound μ g z hμ hg x hM hconc hz hmin
    rwa [nearWeight_eq_site r σ R hr hσ z hz x s hs hnear] at hh
  have hother : ∀ t, t ≠ s → 0 < z t → R/2 < dist t x/r := by
    intro t hts htp
    by_contra hfar
    have hfar' : dist t x/r ≤ R/2 := le_of_not_gt hfar
    have hnear' : σ/4 ≤ dist t x/r := by
      by_contra hh
      exact hts (near_positive_unique r σ R hr hσ z hz x s t hs htp hnear (lt_of_not_ge hh))
    have he := middle_site_zero r σ R γ δ hr hσ hσ1 hR hγ hγσ hδ hδbound μ g z hμ hg x hM hconc hz hmin t hnear' hfar'
    linarith
  have hzx := zero_at_relocation_target r σ R hr hR z hz s x hsx hother
  have hfeas := relocate_feasible r σ R hr hσ hσ1 hR z hz s x hsx hs hnear hother
  have hLγ : L*γ ≤ 1 := by
    have hh := (le_div_iff₀ (by linarith : 0<1+L)).mp hγL
    nlinarith
  have henergy := relocation_integral_loss r σ R γ L hr hσ hσ1 hR hL hγσ hLγ μ g z hμ hg hgLip hz s x hsx hzx hnear hother
  have hmin' := value_le r σ R μ g (relocate r R z s x) hfeas
  rw [←hmin] at hmin'
  have hnonneg : 0 ≤ ∑ p, μ p*(integrand r σ R g (relocate r R z s x) p-integrand r σ R g z p) := by
    unfold objective at hmin'
    have hh := (mul_le_mul_iff_right₀ hr).mp hmin'
    simp_rw [mul_sub,Finset.sum_sub_distrib]
    linarith
  have hb : B ≤ A*(5+L) := relocation_constant_bound σ R L (z s) hσ hσ1 hR hL (by linarith)
  have hpay : B*w*(S-M) ≤ A*(5+L)*w*(S-M) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hw.le) hSM
  have hcap : A*w*(M*w-5*T-(5+L)*(S-M)) ≤ 0 := by
    change (∑ p, μ p*(integrand r σ R g (relocate r R z s x) p-integrand r σ R g z p)) ≤
      -A*(w^2*M-5*w*T)+B*w*(S-M) at henergy
    nlinarith only [henergy,hnonneg,hpay]
  have hnum : M*w ≤ 5*T+(5+L)*(S-M) := by
    by_contra hh
    have hp := mul_pos (mul_pos hA hw) (show 0<M*w-5*T-(5+L)*(S-M) by linarith)
    linarith
  calc
    w ≤ (5*T+(5+L)*(S-M))/M := (le_div_iff₀ hM).mpr (by nlinarith only [hnum])
    _ ≤ ((5+L)*T+(5+L)*(S-M))/M := div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hL hT]) hM.le
    _ = _ := by dsimp [M,S,T]; ring



end
end UniformKServer.PilotCompact

end OAI
