import OAI.Geometry.NodalSets.Elliptic.CorrugationFirstAxis
import OAI.Geometry.NodalSets.Elliptic.CorrugationFrequencyScale
import OAI.Geometry.NodalSets.Elliptic.CorrugationOldData

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem corrugation_local_nonvanishing
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S χ : Coord → ℝ)
    {D U : Set Coord} (hD : IsCompact D) (hconv : Convex ℝ D)
    (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : ∀ y ∈ D, metricGradient g S y ≠ 0)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (amp : ℝ) {L : ℝ} (hL : 0 < L) :
    ∀ᶠ k : ℕ in atTop, ∀ y ∈ D, ∀ x ∈ D,
      ‖x-y‖ ≤ corrugationScale L k →
      ∀ e : Coord ≃L[ℝ] Coord,
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
        (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
        (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x ≠ 0 := by
  obtain ⟨m,hm,B,hB,hslope⟩ := corrugationOldSlope_compact_bounds g S hD hU hDU hg hS hp hn
  obtain ⟨c,hc0,M,hM,hmetric⟩ := compact_metric_comparison g hD (hg.continuousOn.mono hDU)
    (fun y hy ↦ hp y (hDU hy))
  obtain ⟨A,hA,hfreeze⟩ := smooth_compact_covector_freezing S hD hconv hU hDU hS
  obtain ⟨C,hC,hfirst⟩ := corrugation_first_axis_bound χ hχ hc amp
  let K : ℝ := 1+c⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  have ht1 : Tendsto (fun k ↦ A*corrugationScale L k*K) atTop (𝓝 0) := by
    simpa using ((corrugationScale_tendsto L).const_mul A).mul_const K
  have ht2 : Tendsto (fun k ↦ C/(corrugationFrequency k*corrugationScale L k)*K) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (((corrugation_frequency_scale_tendsto hL).inv_tendsto_atTop).const_mul C).mul_const K
  have he1 := ht1.eventually_lt_const (show (0:ℝ) < m/4 by positivity)
  have he2 := ht2.eventually_lt_const (show (0:ℝ) < 1/4 by norm_num)
  filter_upwards [he1,he2] with k hk1 hk2
  intro y hy x hx hxy e he0 he
  let v : Coord := e (Pi.single 0 1)
  let s : ℝ := corrugationOldSlope g S y
  have hs : 0 < s := corrugationOldSlope_positive g S y (hp y (hDU hy)) (hn y hy)
  have hv : ‖v‖ ≤ K := metric_unit_coordinate_bound (g y) hc0 (hmetric y hy).2 v (by simpa [v] using he 0 0)
  have ha : frozenFrameCovector e 2 v = 0 := by dsimp [v]; rw [frozenFrameCovector_axis]; norm_num [Fin.ext_iff]
  have hb : frozenFrameCovector e 3 v = 0 := by dsimp [v]; rw [frozenFrameCovector_axis]; norm_num [Fin.ext_iff]
  have hJ := corrugationFrequency_positive k
  have hR := corrugationScale_positive hL k
  have herr := hfirst s (corrugationFrequency k) (corrugationScale L k) hs.le hJ hR _ _ y x v ha hb
  have hsmall1 : A*corrugationScale L k*K ≤ s/4 := by
    have hm' := (hslope y hy).1
    dsimp [s]
    linarith
  have hsmall2 : s/(corrugationFrequency k*corrugationScale L k)*C*K ≤ s/4 := by
    have hh := mul_le_mul_of_nonneg_left hk2.le hs.le
    calc
      _ = s*(C/(corrugationFrequency k*corrugationScale L k)*K) := by ring
      _ ≤ s*(1/4) := hh
      _ = s/4 := by ring
  have hpos := corrugated_first_axis_positive S χ hχ amp s (corrugationFrequency k)
    (corrugationScale L k) C A K hs hA.le hK.le _ _ y x v
    ((hS.contDiffAt (hU.mem_nhds (hDU hx))).differentiableAt (by simp))
    (corrugation_frozen_axis_differential g S y (hp y (hDU hy)) (hn y hy) e he0)
    (hfreeze x hx y hy v) hxy hv herr (by positivity) hsmall1 hsmall2
  intro hz
  have hpair := metricGradient_pair g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
    s (corrugationFrequency k) (corrugationScale L k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) y)
    x (hp x (hDU hx)) v
  rw [hz,map_zero,zero_apply] at hpair
  change s/2 ≤ fderiv ℝ (S+localizedCorrugation χ (corrugationPeriodicWell amp)
    s (corrugationFrequency k) (corrugationScale L k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x v at hpos
  rw [← hpair] at hpos
  linarith

end
end Yau.Geometry

end OAI
