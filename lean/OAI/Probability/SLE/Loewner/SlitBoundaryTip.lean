import OAI.Probability.SLE.Loewner.InitialDrivingTip

namespace OAI

/-! The static inverse boundary extension takes the actual driver to
the prescribed tip. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

theorem exists_initial_inverse_boundary_tip (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s : unitInterval} (hs : s<1) :
    ∃ B : ℂ → ℂ, ContinuousOn B {z : ℂ | 0 ≤ z.im} ∧
      (∀ z∈upperHalfPlane, B z=initialInverseChart p hi h0 hH s z) ∧
      B (initialDrivingValue p hi h0 hH s hs:ℂ)=p s := by
  by_cases hs0 : s=0
  · subst s
    refine ⟨id,continuous_id.continuousOn,?_,?_⟩
    · intro z _
      simp only [initialInverseChart_zero,id_eq]
    · simp only [id_eq,initialDrivingValue_zero,ofReal_zero,h0]
  obtain ⟨B,hB,hBF⟩ := (initialSlitChart p hi h0 hH s hs0).exists_boundary_extension
  have he (z : ℂ) (hz : z∈upperHalfPlane) : B z=initialInverseChart p hi h0 hH s z := by
    simpa only [initialInverseChart,dite_eq_right hs0] using hBF z hz
  refine ⟨B,hB,he,?_⟩
  let u := initialDrivingValue p hi h0 hH s hs
  have hc : Continuous (fun y : ℝ => (u:ℂ)+(y:ℂ)*I) := by fun_prop
  have hv : Tendsto (fun y : ℝ => (u:ℂ)+(y:ℂ)*I) (𝓝[>] (0:ℝ)) (𝓝 (u:ℂ)) := by
    simpa only [ofReal_zero,zero_mul,add_zero] using
      (hc.tendsto 0).mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds)
  have hm : ∀ᶠ y : ℝ in 𝓝[>] (0:ℝ), (u:ℂ)+(y:ℂ)*I∈{z : ℂ | 0 ≤ z.im} := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    simpa using hy.le
  have hb := (hB (u:ℂ) (by simp)).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hv,hm⟩)
  apply tendsto_nhds_unique hb
  apply (initialInverse_radial_driver_limit p hi h0 hH hs).congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (he _ (by simpa [upperHalfPlane] using hy)).symm

end SLEExactGauge

end

end OAI
