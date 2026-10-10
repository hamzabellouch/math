import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMovingDeformation

namespace OAI

/-! Evaluation of the true canonical family at a converging exterior radius. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radial_uniform_local_evaluation {E : Type*} [MetricSpace E]
    (F : ℕ → ℝ → E) (f : ℝ → E) (L t₀ : ℝ)
    (hF : TendstoUniformlyOn F f atTop (Ici L)) (hf : ContinuousAt f t₀)
    (t : ℕ → ℝ) (ht : Tendsto t atTop (nhds t₀))
    (hmem : ∀ᶠ n in atTop, L ≤ t n) :
    Tendsto (fun n => F n (t n)) atTop (nhds (f t₀)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hu := (Metric.tendstoUniformlyOn_iff.mp hF) (ε/2) (by positivity)
  have hv := (Metric.tendsto_nhds.mp (hf.tendsto.comp ht)) (ε/2) (by positivity)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hu.and (hv.and hmem))
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨h1,h2,h3⟩ := hN n hn
  have h4 := h1 (t n) h3
  calc
    dist (F n (t n)) (f t₀) ≤ dist (F n (t n)) (f (t n))+dist (f (t n)) (f t₀) :=
      dist_triangle _ _ _
    _ < ε/2+ε/2 := add_lt_add (by simpa only [dist_comm] using h4) h2
    _ = ε := by ring

theorem radialShooting_converging_radius (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (nhds z₀)) (r : ℕ → ℝ) (r₀ : ℝ)
    (hr : Tendsto r atTop (nhds r₀)) (hr₀ : innerBoundaryRadius ≤ r₀)
    (hrmem : ∀ᶠ i in atTop, innerBoundaryRadius ≤ r i) :
    Tendsto (fun i => radialExteriorCanonical (radialShootingNu (s i) (z i))
      (s i) (radialShootingM (z i)) (Real.log innerBoundaryRadius) (Real.log (r i)))
      atTop (nhds (radialFreeSlowJet (radialShootingQ z₀) (radialShootingM z₀)
        (Real.log r₀))) := by
  have hν := radialShootingNu_subsequence_tendsto s hs z z₀ hz
  have hm := continuous_radialShootingM.continuousAt.tendsto.comp hz
  obtain ⟨δ,ρ,hδ,hδm,hsmall,hρ,hupper,hlower⟩ := radialShooting_free_annulus z₀
  have hq : -1 < (radialShootingQ z₀).re := by simp [radialShootingQ]
  have hconv := (radialExteriorCanonical_H_limit_subsequence s hs
    (fun i => radialShootingNu (s i) (z i)) (fun i => radialShootingM (z i))
    (radialShootingQ z₀) (radialShootingM z₀) hq hν hm δ ρ
    (Real.log innerBoundaryRadius) hδ hδm hsmall hρ hupper hlower).2
  have hrpos : 0 < r₀ := lt_of_lt_of_le (by linarith [innerBoundaryRadius_bounds.1]) hr₀
  have hlog : Tendsto (fun i => Real.log (r i)) atTop (nhds (Real.log r₀)) :=
    (Real.continuousAt_log hrpos.ne').tendsto.comp hr
  apply radial_uniform_local_evaluation _ _ _ _ hconv
    (radialFreeSlowJet_hasDerivAt _ _ hq _).continuousAt _ hlog
  filter_upwards [hrmem] with i hi
  exact Real.log_le_log (by linarith [innerBoundaryRadius_bounds.1]) hi

end DefocusingNLS

end OAI
