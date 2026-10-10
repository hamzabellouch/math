import OAI.Geometry.RCD.Heat.UniformHeatActionLower
import OAI.Geometry.RCD.Sobolev.UniformMovingValues
import OAI.Geometry.RCD.Heat.HeatActionSlices
import OAI.Geometry.RCD.Metric.CanonicalUniformBallBridge
import OAI.Geometry.RCD.Heat.ScaledLogBridge
import OAI.Geometry.RCD.Sobolev.ShortStepActionError

namespace OAI

/-! # Sharp small-noise lower action along converging endpoint sequences

A hypothetical bad sequence is compared with a uniform law on a small
ball. Its constructed heat limit supplies the sharp main action; the
rough Gaussian bound is used only on the short final step. Both errors
are made arbitrarily small before taking the subsequence.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_moving_log_lower (hK : K ≤ 0)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0)) (x y : X)
    (u v : ℕ → X) (hu : Tendsto u atTop (𝓝 x)) (hv : Tendsto v atTop (𝓝 y))
    {T η : ℝ} (hT : 0 < T) (hT1 : T < 1) (hη : 0 < η) :
    ∀ᶠ k in atTop, -(dist x y)^2/(2*T)-η ≤
      ε k*Real.log (hX.canonicalHeatKernel hn p (ε k*T/2) (u k) (v k)) := by
  classical
  by_contra hbad
  have hfreq : ∃ᶠ k in atTop,
      ε k*Real.log (hX.canonicalHeatKernel hn p (ε k*T/2) (u k) (v k)) < -(dist x y)^2/(2*T)-η := by
    simpa only [not_eventually,not_le] using hbad
  obtain ⟨a,ha,hbad⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨c,D,hc,hD,hbridge⟩ := hX.canonical_uniform_ball_bridge hn p
  obtain ⟨s,r,hs,hsT,hr,_hr1,hcost⟩ := short_step_action_parameters (d := dist x y) (D := D) hT hη
  let μ := hausdorff n X
  let S := closedBall y r
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall y r)
  have hS0 : μ S ≠ 0 := ne_of_gt
    ((hX.fullSupport y r hr).trans_le (measure_mono ball_subset_closedBall))
  have hSf : μ S ≠ ∞ := (hX.finiteOnBounded _ isBounded_closedBall).ne
  obtain ⟨ν,ρ,B,hν,hmap,_hm,_hp,_hb,_hd⟩ :=
    restricted_probability_law μ S measurableSet_closedBall hS0 hSf
  let := hν
  obtain ⟨H,b,hb,hz,hlo,hlim⟩ := hX.uniform_heat_action_lower hn p hK ν hmap y hr
    ball_subset_closedBall hr.le (fun q => by
      have hq : dist (q : X) y ≤ r := q.property
      simpa only [dist_comm] using hq)
    (fun k => ε (a k)) (fun k => hε (a k)) (fun k => hε1 (a k)) (hε0.comp ha.tendsto_atTop)
  let e := fun k => ε (a (b k))
  have he (k : ℕ) : 0 < e k := hε (a (b k))
  have he1 (k : ℕ) : e k ≤ 1 := hε1 (a (b k))
  have he0 : Tendsto e atTop (𝓝 0) := hε0.comp (ha.comp hb).tendsto_atTop
  have hst : s ∈ Ioo (0:ℝ) 1 := ⟨hs,hsT.trans hT1⟩
  have hu' : Tendsto (fun k => u (a (b k))) atTop (𝓝 x) :=
    hu.comp (ha.comp hb).tendsto_atTop
  have hv' : Tendsto (fun k => v (a (b k))) atTop (𝓝 y) :=
    hv.comp (ha.comp hb).tendsto_atTop
  have hxb : ∀ᶠ k in atTop, u (a (b k)) ∈ closedBall y (dist y x+1) := by
    have hh := (tendsto_const_nhds.dist hu').eventually
      (gt_mem_nhds (by linarith : dist y x < dist y x+1))
    filter_upwards [hh] with k hk
    exact mem_closedBall.mpr (by simpa only [dist_comm] using hk.le)
  have hyv := (Metric.tendsto_nhds.mp hv') r hr
  have hvlim := uniform_subtype_moving_values
    (f := fun k z => e k*Real.log (hX.compactHeatFactor hn p ν 1 (e k*s/2)
      (div_pos (mul_pos (he k) hs) (by norm_num)) z))
    (hlim (dist y x+1) (by positivity) s hst) hu' (H.continuous_slice hst).continuousAt hxb
  let A := c*μ.real S/μ.real (ball y (r+1))
  have hA : 0 < A := div_pos (mul_pos hc (ENNReal.toReal_pos hS0 hSf))
    (ENNReal.toReal_pos (hX.fullSupport y (r+1) (by linarith)).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne)
  let E := 2*D*r^2/(T-s)
  have hq : Tendsto (fun k =>
      e k*Real.log (hX.compactHeatFactor hn p ν 1 (e k*s/2)
        (div_pos (mul_pos (he k) hs) (by norm_num)) (u (a (b k)))) + e k*Real.log A-E)
      atTop (𝓝 (H.potential s x-E)) := by
    have hh := (hvlim.add (he0.mul_const (Real.log A))).sub_const E
    simpa only [zero_mul,add_zero] using hh
  have hbound : ∀ᶠ k in atTop,
      e k*Real.log (hX.compactHeatFactor hn p ν 1 (e k*s/2)
        (div_pos (mul_pos (he k) hs) (by norm_num)) (u (a (b k)))) + e k*Real.log A-E ≤
      -(dist x y)^2/(2*T)-η := by
    filter_upwards [hyv] with k hky
    have ht : 0 < e k*(T-s)/2 := div_pos (mul_pos (he k) (sub_pos.mpr hsT)) (by norm_num)
    have ht1 : e k*(T-s)/2 ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_right (he1 k) (sub_pos.mpr hsT).le
      nlinarith
    have hh := hbridge y r hr ν hmap (e k*s/2) (e k*(T-s)/2)
      (div_pos (mul_pos (he k) hs) (by norm_num)) ht ht1 (u (a (b k))) (v (a (b k))) hky.le
    simp only [neg_mul] at hh
    have hlog := scaled_log_bridge (E := D*r^2) (t := e k*(T-s)/2) (he k).le hA
      (hX.compactHeatFactor_positive hn p ν 1 (by intro q; norm_num)
        (e k*s/2) (div_pos (mul_pos (he k) hs) (by norm_num)) (u (a (b k)))) hh
    have htime : e k*s/2+e k*(T-s)/2 = e k*T/2 := by ring
    have herr : e k*(D*r^2)/(e k*(T-s)/2) = E := by
      dsimp only [E]
      field_simp [ne_of_gt (he k),ne_of_gt (sub_pos.mpr hsT)]
    rw [htime,herr] at hlog
    exact hlog.trans (hbad (b k)).le
  have hlast : H.potential s x-E ≤ -(dist x y)^2/(2*T)-η :=
    le_of_tendsto hq hbound
  have hh := hlo s hst x
  rw [dist_comm y x] at hh
  dsimp only [E] at hlast
  have hcost' : -(dist x y)^2/(2*T)-η < -(dist x y)^2/(2*s)-2*D*r^2/(T-s) := by
    rw [neg_div,neg_div]
    linarith
  linarith

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
