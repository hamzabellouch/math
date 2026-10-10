import OAI.Probability.SLE.Loewner.InverseVerticalDifferentiation

namespace OAI

/-! Vertical energy controls separation from a small physical image. -/
noncomputable section
open Set Filter Function Complex Metric MeasureTheory
open scoped Topology ENNReal

namespace SLEExactGauge

lemma holomorphic_vertical_energy {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlane) (x : ℝ) {h y : ℝ}
    (hh : 0<h) (hy : y∈Ioc 0 h)
    (hE : MemLp (fun t : ℝ => deriv F ((x:ℂ)+(t:ℂ)*I)) 2
      (volume.restrict (Ioc 0 h))) :
    ‖F ((x:ℂ)+(h:ℂ)*I)-F ((x:ℂ)+(y:ℂ)*I)‖^2 ≤
      h*(∫ t in Ioc 0 h, ‖deriv F ((x:ℂ)+(t:ℂ)*I)‖^2) := by
  let f := fun t : ℝ => F ((x:ℂ)+(t:ℂ)*I)
  have hn : ∀ᵐ t : ℝ ∂volume.restrict (Ioc 0 h),
      ‖deriv f t‖=‖deriv F ((x:ℂ)+(t:ℂ)*I)‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact holomorphic_vertical_deriv_norm hF x ht.1
  have hd : MemLp (deriv f) 2 (volume.restrict (Ioc 0 h)) :=
    (memLp_congr_norm (measurable_deriv f).aestronglyMeasurable
      hE.aestronglyMeasurable hn).mpr hE
  have hb := complex_interval_energy_oscillation hh hy ⟨hh,le_rfl⟩
    (fun t ht => (holomorphic_vertical_hasDerivAt hF x
      (ordConnected_Ioc.uIcc_subset hy ⟨hh,le_rfl⟩ ht).1).differentiableAt) hd
  have he := integral_congr_ae (hn.mono fun t ht => congrArg (fun r : ℝ => r^2) ht)
  rw [he] at hb
  exact hb

lemma holomorphic_vertical_separation {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlane) (x : ℝ) {h δ ε : ℝ}
    (hh : 0<h) (hδ : 0≤δ) (c : ℂ)
    (hhigh : δ+ε≤‖F ((x:ℂ)+(h:ℂ)*I)-c‖)
    (hlow : ∃ y∈Ioc 0 h, ‖F ((x:ℂ)+(y:ℂ)*I)-c‖≤ε)
    (hE : MemLp (fun t : ℝ => deriv F ((x:ℂ)+(t:ℂ)*I)) 2
      (volume.restrict (Ioc 0 h))) :
    δ^2 ≤ h*(∫ t in Ioc 0 h, ‖deriv F ((x:ℂ)+(t:ℂ)*I)‖^2) := by
  obtain ⟨y,hy,hyc⟩ := hlow
  have htriangle := norm_sub_le_norm_sub_add_norm_sub (F ((x:ℂ)+(h:ℂ)*I))
    (F ((x:ℂ)+(y:ℂ)*I)) c
  have hsep : δ≤‖F ((x:ℂ)+(h:ℂ)*I)-F ((x:ℂ)+(y:ℂ)*I)‖ := by linarith
  exact (pow_le_pow_left₀ hδ hsep 2).trans (holomorphic_vertical_energy hF x hh hy hE)

end SLEExactGauge

end

end OAI
