import OAI.Probability.SLE.Geometry.NormalizedRadiusRestart

namespace OAI

/-! The stopped Green density factors exactly across a normalized restart,
including paths whose deeper radius time is infinite. -/
noncomputable section
open Set Filter
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma IsCapacityTwoWitness.normalized_restart_stopped_green_eq
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (T a : ℝ≥0) (ha : 0 < a)
    (hb : IsCapacityTwoWitness (normalizedRestartDriver U T a) β G' F')
    (κ : ℝ) (w : ℂ) (hwH : w ∈ upperHalfPlane) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 < v)
    (hbase : fullRadius G T (F T ((a:ℂ)*w+(U T:ℂ))) =
      (2*(F T ((a:ℂ)*w+(U T:ℂ))).im)*Real.exp (-u)) :
    greenDensity κ U γ G T (F T ((a:ℂ)*w+(U T:ℂ))) *
        (stoppedGreen κ (normalizedRestartDriver U T a) β G' w v / initialGreen κ w) =
      stoppedGreen κ U γ G (F T ((a:ℂ)*w+(U T:ℂ))) (u+v) := by
  have hbup := normalized_restart_witness T a ha hb
  have haR : 0 < (a:ℝ) := ha
  have hwup : (a:ℂ)*w ∈ upperHalfPlane := by
    change 0 < ((a:ℂ)*w).im
    simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
      using mul_pos haR hwH
  have hV : Continuous (normalizedRestartDriver U T a) := by
    unfold normalizedRestartDriver
    fun_prop
  by_cases hf : radiusLevelTime β G' w v < ∞
  · obtain ⟨t,ht,hR⟩ := exists_live_level_of_radiusLevelTime_lt_top β G' w v hf
    have htu : (a:ℂ)*w ∈ survivingDomain (sourceScaleTrace a β) (a^2*t) := by
      rw [source_scale_domain_iff a _ ha β,source_scale_time_mul_sq a t ha,
        mul_div_cancel_left₀ w (by exact_mod_cast ha.ne' : (a:ℂ)≠0)]
      exact ht
    have hphysical := hw.normalized_restart_level_of_live_source hU T a ha hb w u v hbase t ht hR
    have hgreen := hw.restart_green_composition hU T hbup κ (a^2*t) ((a:ℂ)*w) htu
    have hscale := hb.scaled_green hV a ha κ t w ht
    have hdriver : (fun t => (a:ℝ)*normalizedRestartDriver U T a (sourceScaleTime a t)) =
        (fun t => U (T+t)-U T) := by
      funext r
      unfold normalizedRestartDriver sourceScaleTime
      have htime : a^2*(r/a^2)=r := by field_simp
      rw [htime]
      field_simp
    rw [hdriver] at hscale
    rw [hscale] at hgreen
    rw [stoppedGreen_eq_of_live_level hV hb κ w v t ht hR,
      stoppedGreen_eq_of_live_level hU hw κ _ _ (T+a^2*t)
        (hw.restart_forward_composition T hbup (a^2*t) ((a:ℂ)*w) htu).1 hphysical.1,
      hgreen,hw.restart_green_initial hU T hbup κ ((a:ℂ)*w) hwup,
      initialGreen_pos_real_mul κ a haR w hwH]
    field_simp [(initialGreen_pos κ w hwH).ne']
  · have hp : ¬radiusLevelTime γ G (F T ((a:ℂ)*w+(U T:ℂ))) (u+v)<∞ :=
      fun h => hf ((hw.normalized_restart_radius_finite_iff hU T a ha hb w hwH u v hu hv hbase).mp h)
    simp only [stoppedGreen,ite_eq_right hf,ite_eq_right hp,zero_div,mul_zero]

end SLEExactGauge

end

end OAI
