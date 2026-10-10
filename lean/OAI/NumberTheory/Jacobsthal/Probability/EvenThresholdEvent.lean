import OAI.NumberTheory.Jacobsthal.Estimates.EvenThresholdVolume

namespace OAI

namespace Erdos970

section

namespace ErdosEvenThreshold
open Set MeasureTheory NumberTheoryLean
open FinitePathGeometry DerivativeWeights TransitionKernels FinitePathMeasures KernelDensityBridge

noncomputable def stripDensityBound : ℝ := (5/4:ℝ)*phiEven 2/phiOdd 5
noncomputable def stripConstant : ℝ := 20*stripDensityBound

theorem stripDensityBound_pos : 0 < stripDensityBound := by
  have he := phiEven_pos (by norm_num : (1:ℝ)<2)
  have ho := phiOdd_pos 5
  unfold stripDensityBound
  positivity

theorem stripConstant_pos : 0 < stripConstant := by
  unfold stripConstant
  exact mul_pos (by norm_num) stripDensityBound_pos

theorem oddDensity_compact_bound (s : OddState) {t : ℝ} (ht2 : 2 ≤ t) (ht4 : t ≤ 4) :
    oddDensity s t ≤ stripDensityBound := by
  change (if max 2 (s.1-1) ≤ t then W t*phiEven t/phiOdd s.1 else 0) ≤ _
  by_cases hsupp : max 2 (s.1-1) ≤ t
  · rw [ite_eq_left hsupp]
    have hs5 : s.1 ≤ 5 := by linarith [le_max_right (2:ℝ) (s.1-1)]
    have ht0 : 0 < t := by linarith
    have hW : W t ≤ (5:ℝ)/4 := by
      unfold W
      apply (div_le_div_iff₀ (sq_pos_of_pos ht0) (by norm_num : (0:ℝ)<4)).mpr
      nlinarith
    have hphi : phiEven t ≤ phiEven 2 :=
      phiEven_strictAntiOn.antitoneOn (by norm_num) (by change 1 < t; linarith : t ∈ Ioi (1:ℝ)) ht2
    have hden : phiOdd 5 ≤ phiOdd s.1 := phiOdd_antitone hs5
    have hepos : 0 < phiEven 2 := phiEven_pos (by norm_num)
    have htpos : 0 < phiEven t := phiEven_pos (by linarith)
    have hnum := mul_le_mul hW hphi htpos.le (by norm_num : (0:ℝ)≤5/4)
    calc
      _ ≤ ((5:ℝ)/4*phiEven 2)/phiOdd s.1 := div_le_div_of_nonneg_right hnum (phiOdd_pos _).le
      _ ≤ ((5:ℝ)/4*phiEven 2)/phiOdd 5 :=
        div_le_div_of_nonneg_left (by positivity) (phiOdd_pos 5) hden
      _ = _ := rfl
  · rw [ite_eq_right hsupp]
    exact stripDensityBound_pos.le

theorem oddKernel_strip_bound (s : OddState) {R d : ℝ}
    (hR : 0 < R) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    oddKernel s (thresholdStrip R d) ≤ ENNReal.ofReal (stripConstant*d/R) := by
  rw [oddKernel_apply]
  calc
    _ ≤ ∫⁻ _t in thresholdStrip R d,ENNReal.ofReal stripDensityBound := by
      apply setLIntegral_mono measurable_const
      intro t ht
      have h4 := (strip_parameters hd1 ht).2
      exact ENNReal.ofReal_le_ofReal (oddDensity_compact_bound s ht.1 h4)
    _ = ENNReal.ofReal stripDensityBound*volume (thresholdStrip R d) := by simp
    _ ≤ ENNReal.ofReal stripDensityBound*ENNReal.ofReal (20*d/R) :=
      mul_le_mul_right (thresholdStrip_volume hR hd0 hd1) _
    _ = ENNReal.ofReal (stripConstant*d/R) := by
      rw [← ENNReal.ofReal_mul stripDensityBound_pos.le]
      congr 1
      unfold stripConstant
      ring

theorem oddToEven_strip_bound (s : OddState) {R d : ℝ}
    (hR : 0 < R) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    oddToEven s ((Subtype.val : EvenState → ℝ) ⁻¹' thresholdStrip R d) ≤
      ENNReal.ofReal (stripConstant*d/R) := by
  have hh := oddKernel_strip_bound s hR hd0 hd1
  rw [← oddToEven_map_ratio s,Measure.map_apply measurable_subtype_coe (thresholdStrip_measurable R d)] at hh
  exact hh

theorem exists_uniform_strip_bound : ∃ C : ℝ,0 < C ∧ ∀ R d : ℝ,0 < R → 0 ≤ d → d ≤ 1 →
    ∀ s : OddState,oddToEven s ((Subtype.val : EvenState → ℝ) ⁻¹' thresholdStrip R d) ≤
      ENNReal.ofReal (C*d/R) :=
  ⟨stripConstant,stripConstant_pos,fun _ _ hR hd0 hd1 s => oddToEven_strip_bound s hR hd0 hd1⟩

end ErdosEvenThreshold

end

section

namespace ErdosEvenThreshold
open Set MeasureTheory NumberTheoryLean
open FinitePathGeometry TransitionKernels FinitePathMeasures

noncomputable def nearThreshold (R d : ℝ) : Set ℝ :=
  {t | 1 < nextExponent R t ∧ 0 ≤ thresholdSlack R t ∧ thresholdSlack R t ≤ d}

theorem thresholdStrip_eq_near (R d : ℝ) : thresholdStrip R d=nearThreshold R d := by
  ext t
  constructor
  · intro ht
    exact ht.2
  · rintro ⟨hx,hlo,hhi⟩
    have hm := gap_eq_exponent_mul R t
    have hlow := le_max_left (2*nextExponent R t) (nextExponent R t+2)
    have ht2 : 2 ≤ t := by
      have hh : nextExponent R t*2 ≤ nextExponent R t*t := by
        unfold thresholdSlack at hlo
        nlinarith
      exact le_of_mul_le_mul_left hh (by linarith : 0 < nextExponent R t)
    exact ⟨ht2,hx,hlo,hhi⟩

theorem nearThreshold_measurable (R d : ℝ) : MeasurableSet (nearThreshold R d) := by
  rw [← thresholdStrip_eq_near]
  exact thresholdStrip_measurable R d

theorem conditional_even_near_threshold (s : OddState) {R d : ℝ}
    (hR : 0 < R) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    oddToEven s ((Subtype.val : EvenState → ℝ) ⁻¹' nearThreshold R d) ≤
      ENNReal.ofReal (stripConstant*d/R) := by
  rw [← thresholdStrip_eq_near]
  exact oddToEven_strip_bound s hR hd0 hd1

theorem conditional_even_near_threshold_real (s : OddState) {R d : ℝ}
    (hR : 0 < R) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    (oddToEven s ((Subtype.val : EvenState → ℝ) ⁻¹' nearThreshold R d)).toReal ≤ stripConstant*d/R := by
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (conditional_even_near_threshold s hR hd0 hd1)
  have hnon : 0 ≤ stripConstant*d/R := div_nonneg (mul_nonneg stripConstant_pos.le hd0) hR.le
  simpa only [ENNReal.toReal_ofReal hnon] using hh

theorem exists_conditional_even_bound : ∃ C : ℝ,0 < C ∧ ∀ R d : ℝ,0 < R → 0 ≤ d → d ≤ 1 →
    ∀ s : OddState,(oddToEven s ((Subtype.val : EvenState → ℝ) ⁻¹' nearThreshold R d)).toReal ≤ C*d/R :=
  ⟨stripConstant,stripConstant_pos,fun _ _ hR hd0 hd1 s => conditional_even_near_threshold_real s hR hd0 hd1⟩

end ErdosEvenThreshold

end

end Erdos970

end OAI
