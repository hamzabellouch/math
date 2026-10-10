import OAI.Geometry.RCD.Transport.NearbyEndpointPlan
import OAI.Geometry.RCD.Metric.RescaledBallVolume

namespace OAI

/-! # Nearby endpoint plans with compression normalized on the working ball -/

open Set Filter MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.nearby_normalized_plan {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hK : K ≤ 0) :
    ∃ D : ℝ, 0 < D ∧ ∀ {p x y : X} {r δ : ℝ}, 0 < r →
      -1 ≤ K*(16*r)^2 → 0 < δ → δ ≤ 1/2 →
      dist x p ≤ r/48 → dist y p ≤ r/48 →
      ∃ π : Measure C(Time,X), IsProbabilityMeasure π ∧
        (∀ᵐ γ ∂π, IsGeodesic γ) ∧
        IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
          (π.map (fun γ => (γ 0,γ 1))) ∧
        (∀ t : Time, π.map (fun γ => γ t) ≤
          ENNReal.ofReal ((D/δ^n)/(hausdorff n X).real (ball p (4*r))) • hausdorff n X) ∧
        (∀ᵐ γ ∂π, dist (γ 0) x < δ*r/24 ∧ dist (γ 1) y < δ*r/24 ∧
          (∀ t : Time, dist (γ t) p ≤ r/8)) := by
  let μ := hausdorff n X
  obtain ⟨V,hV,hvol⟩ := hX.rescaled_ball_volume_factor hn (by norm_num : (0:ℝ) ≤ 1)
    (by norm_num : (0:ℝ) < 1/96) (by norm_num : (1/96:ℝ) ≤ 1)
  have hC : 0 < segmentCost n := by unfold segmentCost; positivity
  refine ⟨segmentCost n*V,mul_pos hC (by linarith),?_⟩
  intro p x y r δ hr hcurv hδ hδ1 hx hy
  have hR : 0 < r/24 := by positivity
  have hc4 : -1 ≤ K*(4*(r/24))^2 := by nlinarith
  obtain ⟨π,hπ,hgeo,hopt,hcomp,hends⟩ := hX.nearby_endpoint_plan (p:=p) (x:=x) (y:=y) hn hK hR
    (mul_pos hδ hR) (by nlinarith) (by linarith) (by linarith) hc4
  have hm : 0 < μ.real (ball p (r/24)) := ENNReal.toReal_pos
    (hX.fullSupport _ _ hR).ne' (hX.finiteOnBounded _ isBounded_ball).ne
  have hm4 : 0 < μ.real (ball p (4*r)) := ENNReal.toReal_pos
    (hX.fullSupport _ _ (by positivity)).ne' (hX.finiteOnBounded _ isBounded_ball).ne
  have hv : μ.real (ball p (4*r)) ≤ V*μ.real (ball p (r/24)) := by
    have hh := hvol p (4*r) (by positivity) (by nlinarith : -1 ≤ K*(4*r)^2) p
      (by simpa only [dist_self] using (show 0 ≤ 4*r by positivity))
    simpa only [show (1/96:ℝ)*(4*r)=r/24 by ring] using hh
  have hc : segmentCost n*(r/24)^n/(μ.real (ball p (r/24))*(δ*(r/24))^n) ≤
      ((segmentCost n*V)/δ^n)/μ.real (ball p (4*r)) := by
    have he : segmentCost n*(r/24)^n/(μ.real (ball p (r/24))*(δ*(r/24))^n)=
        (segmentCost n/δ^n)/μ.real (ball p (r/24)) := by
      rw [mul_pow]
      field_simp [hR.ne',hδ.ne',hm.ne']
    rw [he,div_le_div_iff₀ hm hm4]
    have hh := mul_le_mul_of_nonneg_left hv (div_nonneg hC.le (pow_pos hδ n).le)
    convert hh using 1
    ring
  refine ⟨π,hπ,hgeo,hopt,?_,?_⟩
  · intro t
    apply (hcomp t).trans
    apply Measure.le_iff.mpr
    intro S _hS
    simpa only [Measure.smul_apply,smul_eq_mul] using
      mul_le_mul' (ENNReal.ofReal_le_ofReal hc) (le_refl (μ S))
  · filter_upwards [hends] with γ he
    simpa only [show δ*(r/24)=δ*r/24 by ring,show 3*(r/24)=r/8 by ring] using he

end RegularPointCoordinates

end

end OAI
