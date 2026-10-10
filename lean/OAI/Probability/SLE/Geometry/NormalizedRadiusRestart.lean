import OAI.Probability.SLE.Loewner.RestartDomainEquality
import OAI.Probability.SLE.Mass.RestartStoppedMass

namespace OAI

/-! Exact finite radius-time transport through a normalized restart.
The physical and normalized frontiers reach their corresponding levels together. -/
noncomputable section
open Set Filter
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma IsCapacityTwoWitness.scaled_radius_finite_iff
    {U : ℝ≥0 → ℝ} {β : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hb : IsCapacityTwoWitness U β G F) (hU : Continuous U)
    (a : ℝ≥0) (ha : 0 < a) (w : ℂ) (v : ℝ) :
    radiusLevelTime (sourceScaleTrace a β) (sourceScaleChart a G) ((a:ℂ)*w) v < ∞ ↔
      radiusLevelTime β G w v < ∞ := by
  have haC : (a:ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have haR : (a:ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hs := source_scale_witness a ha U β G F hb
  have hsU : Continuous (fun t => (a:ℝ)*U (sourceScaleTime a t)) := by
    unfold sourceScaleTime
    fun_prop
  have htime (t : ℝ≥0) : a^2*sourceScaleTime a t=t := by
    unfold sourceScaleTime
    field_simp
  constructor
  · intro hf
    obtain ⟨t,ht,hR⟩ := exists_live_level_of_radiusLevelTime_lt_top _ _ _ _ hf
    have htlive : w ∈ survivingDomain β (sourceScaleTime a t) := by
      simpa only [source_scale_domain_iff a _ ha β,mul_div_cancel_left₀ w haC] using ht
    have hscaled := hb.scaled_radius a ha (sourceScaleTime a t) w htlive
    rw [htime t,hR] at hscaled
    have hR' : fullRadius G (sourceScaleTime a t) w=(2*w.im)*Real.exp (-v) := by
      apply mul_left_cancel₀ haR
      rw [← hscaled]
      simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
      ring
    rw [radiusLevelTime_eq_of_live_level hU hb w v _ htlive hR']
    exact ENNReal.coe_lt_top
  · intro hf
    obtain ⟨t,ht,hR⟩ := exists_live_level_of_radiusLevelTime_lt_top β G w v hf
    have htlive : (a:ℂ)*w ∈ survivingDomain (sourceScaleTrace a β) (a^2*t) := by
      rw [source_scale_domain_iff a _ ha β,source_scale_time_mul_sq a t ha,
        mul_div_cancel_left₀ w haC]
      exact ht
    have hR' : fullRadius (sourceScaleChart a G) (a^2*t) ((a:ℂ)*w)=
        (2*((a:ℂ)*w).im)*Real.exp (-v) := by
      rw [hb.scaled_radius a ha t w ht,hR]
      simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
      ring
    rw [radiusLevelTime_eq_of_live_level hsU hs _ v _ htlive hR']
    exact ENNReal.coe_lt_top

lemma IsCapacityTwoWitness.normalized_restart_radius_finite_iff
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (T a : ℝ≥0) (ha : 0 < a)
    (hb : IsCapacityTwoWitness (normalizedRestartDriver U T a) β G' F')
    (w : ℂ) (hwH : w ∈ upperHalfPlane) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 < v)
    (hbase : fullRadius G T (F T ((a:ℂ)*w+(U T:ℂ))) =
      (2*(F T ((a:ℂ)*w+(U T:ℂ))).im)*Real.exp (-u)) :
    radiusLevelTime γ G (F T ((a:ℂ)*w+(U T:ℂ))) (u+v) < ∞ ↔
      radiusLevelTime β G' w v < ∞ := by
  have hscaled := normalized_restart_witness T a ha hb
  have hwup : (a:ℂ)*w ∈ upperHalfPlane := by
    change 0 < ((a:ℂ)*w).im
    simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
      using mul_pos (show (0:ℝ)<a from ha) hwH
  rw [hw.restart_radius_finite_iff hU T hscaled _ hwup u v hu hv hbase]
  apply hb.scaled_radius_finite_iff
  unfold normalizedRestartDriver
  fun_prop
  exact ha

lemma IsCapacityTwoWitness.normalized_restart_radius_time
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (T a : ℝ≥0) (ha : 0 < a)
    (hb : IsCapacityTwoWitness (normalizedRestartDriver U T a) β G' F')
    (w : ℂ) (hwH : w ∈ upperHalfPlane) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 < v)
    (hbase : fullRadius G T (F T ((a:ℂ)*w+(U T:ℂ))) =
      (2*(F T ((a:ℂ)*w+(U T:ℂ))).im)*Real.exp (-u)) :
    radiusLevelTime γ G (F T ((a:ℂ)*w+(U T:ℂ))) (u+v) =
      (T:ℝ≥0∞)+(a:ℝ≥0∞)^2*radiusLevelTime β G' w v := by
  have hV : Continuous (normalizedRestartDriver U T a) := by
    unfold normalizedRestartDriver
    fun_prop
  by_cases hf : radiusLevelTime β G' w v < ∞
  · obtain ⟨t,ht,hR⟩ := exists_live_level_of_radiusLevelTime_lt_top β G' w v hf
    rw [radiusLevelTime_eq_of_live_level hV hb w v t ht hR,
      (hw.normalized_restart_level_of_live_source hU T a ha hb w u v hbase t ht hR).2]
    simp only [ENNReal.coe_add,ENNReal.coe_mul,ENNReal.coe_pow]
  · have hp : ¬radiusLevelTime γ G (F T ((a:ℂ)*w+(U T:ℂ))) (u+v)<∞ :=
      fun h => hf ((hw.normalized_restart_radius_finite_iff hU T a ha hb w hwH u v hu hv hbase).mp h)
    rw [not_lt_top_iff.mp hf,not_lt_top_iff.mp hp,ENNReal.mul_top,add_top]
    exact pow_ne_zero _ (by exact_mod_cast ha.ne')

end SLEExactGauge

end

end OAI
