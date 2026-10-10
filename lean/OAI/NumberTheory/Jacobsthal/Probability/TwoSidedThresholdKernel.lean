import OAI.NumberTheory.Jacobsthal.Partitions.TwoSidedThresholdGeometry
import OAI.NumberTheory.Jacobsthal.Paths.ActualThresholdArrival

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.TwoSidedThresholdKernel
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures TransitionKernels KernelDensityBridge DerivativeWeights
open TwoSidedThresholdGeometry ErdosEvenThreshold CanonicalGapExposure RegeneratingInverseBands
attribute [local instance] Classical.propDecidable

noncomputable def thickDensityBound : ℝ := (3/2:ℝ)*phiEven 2/phiOdd 6
noncomputable def thickConstant : ℝ := 42*thickDensityBound

theorem thickDensityBound_pos : 0 < thickDensityBound := by
  have he := phiEven_pos (by norm_num : (1:ℝ)<2)
  have ho := phiOdd_pos 6
  unfold thickDensityBound
  positivity

theorem thickConstant_pos : 0 < thickConstant := by
  unfold thickConstant
  exact mul_pos (by norm_num) thickDensityBound_pos

theorem oddDensity_thick_bound (s : OddState) {t : ℝ} (ht2 : 2 ≤ t) (ht5 : t ≤ 5) :
    oddDensity s t ≤ thickDensityBound := by
  change (if max 2 (s.1-1) ≤ t then W t*phiEven t/phiOdd s.1 else 0) ≤ _
  by_cases hsup : max 2 (s.1-1) ≤ t
  · rw [ite_eq_left hsup]
    have hs6 : s.1 ≤ 6 := by linarith [le_max_right (2:ℝ) (s.1-1)]
    have ht0 : 0 < t := by linarith
    have hW : W t ≤ (3:ℝ)/2 := by
      unfold W
      apply (div_le_div_iff₀ (sq_pos_of_pos ht0) (by norm_num : (0:ℝ)<2)).mpr
      nlinarith
    have hphi := phiEven_strictAntiOn.antitoneOn (by norm_num : (2:ℝ) ∈ Ioi 1)
      (by change 1 < t; linarith : t ∈ Ioi (1:ℝ)) ht2
    have hden := phiOdd_antitone hs6
    have hnum := mul_le_mul hW hphi (phiEven_pos (by linarith : 1 < t)).le (by norm_num : (0:ℝ)≤3/2)
    calc
      _ ≤ ((3:ℝ)/2*phiEven 2)/phiOdd s.1 := div_le_div_of_nonneg_right hnum (phiOdd_pos _).le
      _ ≤ ((3:ℝ)/2*phiEven 2)/phiOdd 6 :=
        div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (phiEven_pos (by norm_num)).le) (phiOdd_pos 6) hden
      _ = _ := rfl
  · rw [ite_eq_right hsup]
    exact thickDensityBound_pos.le

theorem oddKernel_thick_bound (s : OddState) {R delta : ℝ} (hR : 3 ≤ R) (hd : 0 ≤ delta) :
    oddKernel s (thickStrip R delta) ≤ ENNReal.ofReal (thickConstant*delta) := by
  rw [oddKernel_apply]
  calc
    _ ≤ ∫⁻ _t in thickStrip R delta,ENNReal.ofReal thickDensityBound := by
      apply setLIntegral_mono measurable_const
      intro t ht
      exact ENNReal.ofReal_le_ofReal (oddDensity_thick_bound s ht.1 ht.2.1)
    _ = ENNReal.ofReal thickDensityBound*volume (thickStrip R delta) := by simp
    _ ≤ ENNReal.ofReal thickDensityBound*ENNReal.ofReal (42*delta) :=
      mul_le_mul_right (thickStrip_volume hR hd) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul thickDensityBound_pos.le]
      congr 1
      unfold thickConstant
      ring

theorem oddToEven_thick_bound (s : OddState) {R delta : ℝ} (hR : 3 ≤ R) (hd : 0 ≤ delta) :
    oddToEven s ((Subtype.val : EvenState → ℝ) ⁻¹' thickStrip R delta) ≤ ENNReal.ofReal (thickConstant*delta) := by
  have hh := oddKernel_thick_bound s hR hd
  rw [← oddToEven_map_ratio s,Measure.map_apply measurable_subtype_coe (thickStrip_measurable R delta)] at hh
  exact hh

theorem oddToEven_thick_zero_high_parent (s : OddState) {R delta : ℝ} (hs : 6 < s.1) :
    oddToEven s ((Subtype.val : EvenState → ℝ) ⁻¹' thickStrip R delta)=0 := by
  have he : oddToEven s ((Subtype.val : EvenState → ℝ) ⁻¹' thickStrip R delta)=oddKernel s (thickStrip R delta) := by
    rw [← oddToEven_map_ratio s,Measure.map_apply measurable_subtype_coe (thickStrip_measurable R delta)]
  rw [he,oddKernel_apply]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (thickStrip_measurable R delta)] with t ht
  have hn : ¬max 2 (s.1-1) ≤ t := by linarith [le_max_right (2:ℝ) (s.1-1),ht.2.1]
  have hz : oddDensity s t=0 := ite_eq_right hn
  simp only [hz,ENNReal.ofReal_zero,Pi.zero_apply]
end NumberTheoryLean.TwoSidedThresholdKernel

end

end Erdos970

end OAI
