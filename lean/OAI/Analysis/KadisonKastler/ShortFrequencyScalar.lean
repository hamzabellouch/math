import OAI.Analysis.KadisonKastler.FrequencyPacketTensor

namespace OAI

/-! # Unit scalar packets in arbitrarily short frequency intervals -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

def shortFrequencyIndicator (δ : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  indicatorConstLp (s:=Set.Ioc 0 (δ/(2*Real.pi))) 2 measurableSet_Ioc
    (measure_Ioc_lt_top (μ:=volume)).ne (1 : ℂ)

theorem shortFrequencyIndicator_norm_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < ‖shortFrequencyIndicator δ‖ := by
  rw [shortFrequencyIndicator,norm_indicatorConstLp (by norm_num) (by norm_num)]
  have hwidth : 0 < δ/(2*Real.pi) := by positivity
  have hv : 0 < (volume : Measure ℝ).real (Set.Ioc 0 (δ/(2*Real.pi))) := by
    simpa only [measureReal_def,Real.volume_Ioc,sub_zero,ENNReal.toReal_ofReal hwidth.le] using hwidth
  exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hv _)

theorem shortFrequencyIndicator_low (δ : ℝ) :
    regularIndicatorProjection (Set.Ioi (0 : ℝ)) measurableSet_Ioi (shortFrequencyIndicator δ)=
      shortFrequencyIndicator δ := by
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae _ measurableSet_Ioi (shortFrequencyIndicator δ),
    indicatorConstLp_coeFn (p:=2) (s:=Set.Ioc 0 (δ/(2*Real.pi))) (μ:=volume)
      (hs:=measurableSet_Ioc) (hμs:=(measure_Ioc_lt_top (μ:=volume)).ne) (c:=(1 : ℂ))]
    with t hp hf
  change shortFrequencyIndicator δ t=_ at hf
  rw [hp]
  by_cases ht : 0 < t
  · exact Set.indicator_of_mem ht _
  · rw [Set.indicator_of_notMem (show t ∉ Set.Ioi (0 : ℝ) from ht)]
    exact (hf.trans (Set.indicator_of_notMem (fun h => ht h.1) _)).symm

theorem shortFrequencyIndicator_high (δ : ℝ) :
    regularIndicatorProjection (Set.Ioi (δ/(2*Real.pi))) measurableSet_Ioi
      (shortFrequencyIndicator δ)=0 := by
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae _ measurableSet_Ioi (shortFrequencyIndicator δ),
    indicatorConstLp_coeFn (p:=2) (s:=Set.Ioc 0 (δ/(2*Real.pi))) (μ:=volume)
      (hs:=measurableSet_Ioc) (hμs:=(measure_Ioc_lt_top (μ:=volume)).ne) (c:=(1 : ℂ)),
    Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with t hp hf hz
  change shortFrequencyIndicator δ t=_ at hf
  rw [hp,hz]
  by_cases ht : δ/(2*Real.pi) < t
  · rw [Set.indicator_of_mem (show t ∈ Set.Ioi (δ/(2*Real.pi)) from ht),hf,
      Set.indicator_of_notMem (show t ∉ Set.Ioc 0 (δ/(2*Real.pi)) from fun h => not_le_of_gt ht h.2)]
    rfl
  · exact Set.indicator_of_notMem (show t ∉ Set.Ioi (δ/(2*Real.pi)) from ht) _

theorem exists_short_frequency_scalar {δ : ℝ} (hδ : 0 < δ) :
    ∃ φ : Lp ℂ 2 (volume : Measure ℝ), ‖φ‖=1 ∧
      regularFrequencyProjection 0 φ=φ ∧ regularFrequencyProjection δ φ=0 := by
  let f := shortFrequencyIndicator δ
  let c : ℂ := (‖f‖⁻¹ : ℝ)
  let g := c • f
  let e := Lp.fourierTransformₗᵢ ℝ ℂ
  have hf : 0 < ‖f‖ := shortFrequencyIndicator_norm_pos hδ
  have hg : ‖g‖=1 := by
    change ‖c • f‖=1
    rw [norm_smul]
    change ‖((‖f‖⁻¹ : ℝ) : ℂ)‖*‖f‖=1
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hf),inv_mul_cancel₀ hf.ne']
  refine ⟨e.symm g,by rwa [e.symm.norm_map],?_,?_⟩
  · change e.symm (regularIndicatorProjection (Set.Ioi (0/(2*Real.pi))) measurableSet_Ioi
      (e (e.symm g)))=e.symm g
    rw [e.apply_symm_apply]
    congr 1
    simp only [zero_div]
    change regularIndicatorProjection (Set.Ioi (0 : ℝ)) measurableSet_Ioi (c • f)=c • f
    rw [map_smul,shortFrequencyIndicator_low]
  · change e.symm (regularIndicatorProjection (Set.Ioi (δ/(2*Real.pi))) measurableSet_Ioi
      (e (e.symm g)))=0
    rw [e.apply_symm_apply]
    change e.symm (regularIndicatorProjection (Set.Ioi (δ/(2*Real.pi))) measurableSet_Ioi
      (c • f))=0
    rw [map_smul,shortFrequencyIndicator_high,smul_zero,map_zero]

end

end KadisonKastler

end OAI
