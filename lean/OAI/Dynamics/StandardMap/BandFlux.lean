import OAI.Dynamics.StandardMap.IntensityBounds

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma band_fine_lower (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000))
    (hT:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) {α:ℝ} (ha:0≤α) (ha1:α≤1)
    (t:DyadicTime) (ht:0<(t:ℝ)) (ht1:(t:ℝ)≤1/2) :
    (bandIntensity μ (Ico 0 1)).toReal/2≤∫d,bandCap α t d ∂bandLaw μ := by
  let E:Set NonAffineArray := {d | endpointLeft d.val∈Ico (-1/2) 0}
  have hE : MeasurableSet E := (measurable_endpointLeft.comp measurable_subtype_coe) measurableSet_Ico
  have hh := setIntegral_le_integral (s:=E) (bandCap_integrable μ hs hT ha ha1 t ht) (bandCap_nonneg ha ha1 t ht)
  have he : bandCap α t=ᵐ[(bandLaw μ).restrict E] (fun _ => (1:ℝ)) := by
    filter_upwards [ae_restrict_mem hE,ae_restrict_of_ae (ae_restrict_mem (measurableSet_lengthBand 0)),ae_restrict_of_ae (ae_restrict_of_ae hs)] with d he hd hsd
    exact bandCap_one_fine d hd hsd he t ht ht1
  rw [integral_congr_ae he,integral_const] at hh
  simp only [smul_eq_mul,mul_one,measureReal_def,Measure.restrict_apply_univ] at hh
  rw [bandLaw_endpoint_map μ _ measurableSet_Ico,stationary_half_real _ (bandIntensity_translate μ hT) (bandIntensity_finite μ hs)] at hh
  exact hh
lemma band_coarse_upper (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000))
    (hT:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ)
    (htree:∀ᵐd ∂μ,TreeArray d.val) (hcan:∀ᵐd ∂μ,NoFastCancellation (realArray d.val) (1/100000000))
    {α:ℝ} (ha:0≤α) (ha1:α≤1) (n:ℕ) (hn:0<n) (hsmall:1200000004/(n:ℝ)≤1/10000) :
    (∫d,bandCap α (dyadicInt n) d ∂bandLaw μ)≤
      (α*1200000004/(n:ℝ))*((n:ℝ)+3)*(bandIntensity μ (Ico 0 1)).toReal := by
  let t:DyadicTime := dyadicInt n
  have ht:0<(t:ℝ) := by simpa only [t,dyadicInt_val,Int.cast_natCast] using (Nat.cast_pos.mpr hn : (0:ℝ)<n)
  let E:Set NonAffineArray := {d | endpointLeft d.val∈Icc (-2) (n:ℝ)}
  have hE : MeasurableSet E := (measurable_endpointLeft.comp measurable_subtype_coe) measurableSet_Icc
  have hf : bandLaw μ E<∞ := bandLaw_endpoint_finite μ hs hT _ _
  have : IsFiniteMeasure ((bandLaw μ).restrict E) := ⟨by simpa only [Measure.restrict_apply_univ] using hf⟩
  let C:ℝ := α*1200000004/(n:ℝ)
  have hC:0≤C := by dsimp [C]; positivity
  have hi : Integrable (E.indicator (fun _ => C)) (bandLaw μ) := IntegrableOn.integrable_indicator (integrable_const (μ:=(bandLaw μ).restrict E) C) hE
  have hg : bandCap α t≤ᵐ[bandLaw μ] E.indicator (fun _ => C) := by
    filter_upwards [ae_restrict_mem (measurableSet_lengthBand 0),ae_restrict_of_ae hs,ae_restrict_of_ae htree,ae_restrict_of_ae hcan] with d hd hsd htd hcd
    by_cases he:d∈E
    · rw [indicator_of_mem he]
      have hb := band_shortfall_bound d hd hsd htd hcd t ht
      have hx : (t:ℝ)=(n:ℝ) := by simp only [t,dyadicInt_val,Int.cast_natCast]
      rw [hx] at hb
      rw [bandCap,entropyCap_linear (hb.trans hsmall)]
      exact (mul_le_mul_of_nonneg_left hb ha).trans_eq (by unfold C; ring)
    · rw [indicator_of_notMem he]
      exact le_of_eq (band_cap_support α d hd hsd t ht he)
  have hb := integral_mono_ae (bandCap_integrable μ hs hT ha ha1 t ht) hi hg
  rw [integral_indicator hE,integral_const] at hb
  simp only [smul_eq_mul,measureReal_def,Measure.restrict_apply_univ] at hb
  have hm : (bandLaw μ E).toReal≤((n:ℝ)+3)*(bandIntensity μ (Ico 0 1)).toReal := by
    rw [bandLaw_endpoint_map μ _ measurableSet_Icc]
    exact stationary_interval_real_upper _ (bandIntensity_translate μ hT) (bandIntensity_finite μ hs) n
  exact hb.trans ((mul_le_mul_of_nonneg_right hm hC).trans_eq (by unfold C; ring))
end StandardMapEntropy

end OAI
