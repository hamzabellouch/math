import OAI.Probability.SLE.Loewner.InitialInverseTimeContinuity
import OAI.Probability.SLE.Loewner.InitialChartIdentities

namespace OAI

/-! Continuity of the forward coordinates along any sequence of surviving
points, using the actual inverse charts and Hurwitz's theorem. -/
noncomputable section
open Set Filter Function Metric
open scoped Topology

namespace SLEExactGauge

theorem initialForwardChart_tendsto (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {s : unitInterval} (ht : Tendsto t atTop (𝓝 s))
    {z : ℕ → ℂ} {a : ℂ} (hz : Tendsto z atTop (𝓝 a))
    (ha : a∈upperHalfPlane \ range (initialSubarc p s))
    (hzD : ∀ n, z n∈upperHalfPlane \ range (initialSubarc p (t n))) :
    Tendsto (fun n => initialForwardChart p hi h0 hH (t n) (z n))
      atTop (𝓝 (initialForwardChart p hi h0 hH s a)) := by
  have hbase := initialInverseChart_locallyUniform_continuous p hi h0 hH s
  have hconv : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      (initialInverseChart p hi h0 hH s) atTop upperHalfPlane := by
    intro U hU w hw
    obtain ⟨V,hV,hN⟩ := hbase U hU w hw
    exact ⟨V,hV,ht.eventually hN⟩
  have hconst := hz.tendstoUniformlyOn_const upperHalfPlane |>.tendstoLocallyUniformlyOn
  have hdiff := hconv.sub hconst
  have hnc : ¬ ∀ w∈upperHalfPlane, initialInverseChart p hi h0 hH s w-a=0 := by
    intro h
    exact initialInverse_limit_not_constant p hi h0 hH hconv a
      (fun w hw => sub_eq_zero.mp (h w hw))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hevent := TauCeti.hurwitz_eventually_exists_eq_zero isOpen_upperHalfPlane
    (convex_halfSpace_im_gt (0:ℝ)).isPreconnected
    (Eventually.of_forall fun n => (initialInverseChart_differentiableOn p hi h0 hH (t n)).sub_const (z n))
    hdiff (initialForwardChart_mem_upper p hi h0 hH s ha)
    (sub_eq_zero.mpr (initialInverse_forward_at p hi h0 hH s ha)) hnc hε
  filter_upwards [hevent] with n hn
  obtain ⟨w,hw,hew⟩ := hn
  have he : w=initialForwardChart p hi h0 hH (t n) (z n) := by
    apply initialInverseChart_injOn p hi h0 hH (t n) hw.1
      (initialForwardChart_mem_upper p hi h0 hH (t n) (hzD n))
    exact (sub_eq_zero.mp hew).trans (initialInverse_forward_at p hi h0 hH (t n) (hzD n)).symm
  simpa only [← he,mem_ball] using hw.2

end SLEExactGauge

end

end OAI
