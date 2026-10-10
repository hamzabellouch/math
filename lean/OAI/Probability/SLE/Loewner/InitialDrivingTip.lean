import OAI.Probability.SLE.Loewner.CapacityLoewnerIntegral
import OAI.Probability.SLE.Loewner.SlitChartBoundaryExtension

namespace OAI

/-! The radial inverse limit at the proved driving value is the prescribed
simple-arc tip. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

theorem initialInverse_radial_driver_limit (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s : unitInterval} (hs : s<1) :
    Tendsto (fun y : ℝ => initialInverseChart p hi h0 hH s
      ((initialDrivingValue p hi h0 hH s hs:ℂ)+(y:ℂ)*I))
      (𝓝[>] (0:ℝ)) (𝓝 (p s)) := by
  by_cases hs0 : s=0
  · subst s
    simp only [initialInverseChart_zero,initialDrivingValue_zero,ofReal_zero,zero_add,h0,id_eq]
    have hh := (Complex.continuous_ofReal.tendsto 0).mul_const I
    simpa only [ofReal_zero,zero_mul] using hh.mono_left nhdsWithin_le_nhds
  obtain ⟨B,hB,hBF⟩ := (initialSlitChart p hi h0 hH s hs0).exists_boundary_extension
  have hBe : ∀ z∈upperHalfPlane, B z=initialInverseChart p hi h0 hH s z := by
    intro z hz
    simpa only [initialInverseChart,dite_eq_right hs0] using hBF z hz
  let u := initialDrivingValue p hi h0 hH s hs
  have hG := initialDrivingValue_spec p hi h0 hH s hs
  have hGmem : ∀ᶠ r : ℝ in 𝓝[>] (0:ℝ),
      initialForwardChart p hi h0 hH s (p (slitFutureParameter s r))∈{z : ℂ | 0≤z.im} := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds
      (gt_mem_nhds (sub_pos.mpr (show (s:ℝ)<1 from hs)))] with r hr hrd
    exact (show 0<(initialForwardChart p hi h0 hH s
      (p (slitFutureParameter s r))).im from initialForwardChart_mem_upper p hi h0 hH s
        (slitFuturePoint_mem_domain p hi hH s ⟨hr,hrd⟩)).le
  have hBg := (hB (u:ℂ) (by simp)).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hG,hGmem⟩)
  have hphysical : Tendsto (fun r : ℝ => p (slitFutureParameter s r))
      (𝓝[>] (0:ℝ)) (𝓝 (p s)) := by
    have hc : Continuous (fun r : ℝ => p (slitFutureParameter s r)) :=
      p.continuous.comp (slitFutureParameter_continuous s)
    simpa only [slitFutureParameter_zero] using
      (hc.tendsto 0).mono_left (show 𝓝[>] (0:ℝ)≤𝓝 (0:ℝ) from nhdsWithin_le_nhds)
  have heq : B (u:ℂ)=p s := by
    apply tendsto_nhds_unique hBg
    apply hphysical.congr'
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds
      (gt_mem_nhds (sub_pos.mpr (show (s:ℝ)<1 from hs)))] with r hr hrd
    have hd := slitFuturePoint_mem_domain p hi hH s (show r∈Ioo 0 (1-(s:ℝ)) from ⟨hr,hrd⟩)
    symm
    change B (initialForwardChart p hi h0 hH s (p (slitFutureParameter s r)))=
      p (slitFutureParameter s r)
    rw [hBe _ (initialForwardChart_mem_upper p hi h0 hH s hd),initialInverse_forward_at p hi h0 hH s hd]
  have hzlim : Tendsto (fun y : ℝ => (u:ℂ)+(y:ℂ)*I) (𝓝[>] (0:ℝ)) (𝓝 (u:ℂ)) := by
    have hc : Continuous (fun y : ℝ => (u:ℂ)+(y:ℂ)*I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    simpa only [ofReal_zero,zero_mul,add_zero] using
      (hc.tendsto 0).mono_left
        (show 𝓝[>] (0:ℝ)≤𝓝 (0:ℝ) from nhdsWithin_le_nhds)
  have hzmem : ∀ᶠ y : ℝ in 𝓝[>] (0:ℝ), (u:ℂ)+(y:ℂ)*I∈{z : ℂ | 0≤z.im} := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    simpa using hy.le
  have hh := (hB (u:ℂ) (by simp)).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hzlim,hzmem⟩)
  rw [heq] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact hBe _ (by simpa [upperHalfPlane] using hy)

end SLEExactGauge

end

end OAI
