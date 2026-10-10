import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorShootingFamily

namespace OAI

/-! Uniform outgoing convergence can be evaluated at radii tending to infinity. -/

open Set Filter
namespace DefocusingNLS

theorem radial_uniform_moving_limit {E : Type*} [MetricSpace E]
    (F : ℕ → ℝ → E) (f : ℝ → E) (m : E) (L : ℝ)
    (hF : TendstoUniformlyOn F f atTop (Ici L))
    (hf : Tendsto f atTop (nhds m)) (t : ℕ → ℝ)
    (ht : Tendsto t atTop atTop) :
    Tendsto (fun n => F n (t n)) atTop (nhds m) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hu := (Metric.tendstoUniformlyOn_iff.mp hF) (ε/2) (by positivity)
  have hv := (Metric.tendsto_nhds.mp (hf.comp ht)) (ε/2) (by positivity)
  have hL := ht.eventually (eventually_ge_atTop L)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hu.and (hv.and hL))
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨h1,h2,h3⟩ := hN n hn
  have h4 := h1 (t n) h3
  calc
    dist (F n (t n)) m ≤ dist (F n (t n)) (f (t n))+dist (f (t n)) m :=
      dist_triangle _ _ _
    _ < ε/2+ε/2 := add_lt_add (by simpa only [dist_comm] using h4) h2
    _ = ε := by ring

theorem radialFreeSlowJet_tendsto (q m : ℂ) (hq : -1 < q.re) :
    Tendsto (radialFreeSlowJet q m) atTop (nhds (m,0)) := by
  obtain ⟨C,_hC,hbound⟩ := radialFreeSlowJet_remainder q m hq 0
  have he : Tendsto (fun t : ℝ => C*Real.exp (-4*t)) atTop (nhds 0) := by
    have hh := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (show (0 : ℝ)<4 by norm_num))).const_mul C
    simpa only [mul_zero,neg_mul,Function.comp_def,id_eq] using hh
  have hd : Tendsto
      (fun t => radialFreeSlowJet q m t-radialPolynomialJet (radialFreeExpansion (-2*q) m 1) t)
      atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ he
    filter_upwards [eventually_ge_atTop (Real.log 4/2)] with t ht
    simpa only [Nat.reduceAdd,Nat.cast_ofNat,show -(2*(2 : ℝ))*t = -4*t by ring]
      using hbound t ht
  have hp : Tendsto (radialPolynomialJet (radialFreeExpansion (-2*q) m 1))
      atTop (nhds (m,0)) := by
    simpa only [radialFreeExpansion_constant] using
      radialPolynomialJet_tendsto (radialFreeExpansion (-2*q) m 1)
  simpa only [sub_add_cancel,zero_add] using hd.add hp

theorem radialShooting_moving_tail (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileCertificate.ProfileMatchingBall)
    (z₀ : ProfileCertificate.ProfileMatchingBall)
    (hz : Tendsto z atTop (nhds z₀)) (t : ℕ → ℝ)
    (ht : Tendsto t atTop atTop) :
    Tendsto (fun i => radialExteriorCanonical (radialShootingNu (s i) (z i))
      (s i) (radialShootingM (z i)) (Real.log innerBoundaryRadius) (t i))
      atTop (nhds (radialShootingM z₀,0)) := by
  have hq := continuous_radialShootingQ.continuousAt.tendsto.comp hz
  have hm := continuous_radialShootingM.continuousAt.tendsto.comp hz
  have hν : Tendsto (fun i => radialShootingNu (s i) (z i))
      atTop (nhds (-2*radialShootingQ z₀)) := by
    simpa only [radialShootingNu,Function.comp_def,sub_zero] using!
      (hq.const_mul (-2)).sub
        ((tendsto_one_div_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1/(n : ℂ)) atTop (nhds 0)).comp hs.tendsto_atTop)
  obtain ⟨δ,ρ,hδ,hδm,hsmall,hρ,hupper,hlower⟩ := radialShooting_free_annulus z₀
  have hq0 : -1 < (radialShootingQ z₀).re := by simp [radialShootingQ]
  have hconv := (radialExteriorCanonical_H_limit_subsequence s hs
    (fun i => radialShootingNu (s i) (z i)) (fun i => radialShootingM (z i))
    (radialShootingQ z₀) (radialShootingM z₀) hq0 hν hm δ ρ
    (Real.log innerBoundaryRadius) hδ hδm hsmall hρ hupper hlower).2
  exact radial_uniform_moving_limit _ _ _ _ hconv
    (radialFreeSlowJet_tendsto _ _ hq0) t ht

end DefocusingNLS

end OAI
