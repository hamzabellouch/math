import OAI.Geometry.Perimeter.Regularity.RawConeLink

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
namespace RPISingularHarnack
namespace SphericalFrankel

lemma minimizing_perimeter_singleton {n : ℕ} (hn : 1 < n) {E : Set (Euc n)}
    (hE : IsLocallyPerimeterMinimizing E) (x : Euc n) : perimeterMeasure E {x} = 0 := by
  obtain ⟨C, D, hC0, hCt, hD0, hDt, hCD⟩ := minimizing_perimeter_hausdorff_comparison hn
  have hd : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast (by omega : 0 < n-1)
  let := Measure.nullSingletonClass_hausdorff (Euc n) hd
  apply le_antisymm _ zero_le
  calc
    perimeterMeasure E {x} ≤ (C • (Measure.hausdorffMeasure (n-1 : ℕ)).restrict
        (perimeterSupport E)) {x} := (hCD E hE).1 {x}
    _ = 0 := by simp

lemma minimizing_support_nonzero_point {n : ℕ} (hn : 1 < n) {E : Set (Euc n)}
    (hE : IsLocallyPerimeterMinimizing E) (hv : (0 : Euc n) ∈ perimeterSupport E) :
    ∃ x ∈ perimeterSupport E, x ≠ 0 := by
  have hv' : (0 : Euc n) ∈ (perimeterMeasure E).support := by
    rwa [perimeterMeasure_support]
  have hp := Metric.nhds_basis_ball.mem_measureSupport.mp hv' 1 (by norm_num : (0 : ℝ)<1)
  have hdiff : 0 < perimeterMeasure E (Metric.ball 0 1 \ {(0 : Euc n)}) := by
    rwa [measure_sdiff_null (minimizing_perimeter_singleton hn hE 0)]
  obtain ⟨x, hx, hs⟩ := (perimeterMeasure E).nonempty_inter_support_of_pos hdiff
  exact ⟨x, by rwa [perimeterMeasure_support] at hs, hx.2⟩

lemma annularWeight_pos {n : ℕ} {x : Euc n} (h1 : 1 < ‖x‖) (h2 : ‖x‖ < 2) :
    0 < annularWeight x := by
  unfold annularWeight annularCut annularProfile
  apply mul_pos
  · apply mul_pos <;> apply expNegInvGlue.pos_of_pos
    · nlinarith [norm_nonneg x]
    · nlinarith [norm_nonneg x]
  · exact inv_pos.mpr (lt_trans (by norm_num) h1)

lemma cone_support_annular_point {n : ℕ} (hn : 1 < n) {E : Set (Euc n)}
    (hE : IsLocallyPerimeterMinimizing E) (hc : IsCone E)
    (hv : (0 : Euc n) ∈ perimeterSupport E) :
    ∃ y ∈ perimeterSupport E, ‖y‖ = (3 : ℝ)/2 := by
  obtain ⟨x, hx, hx0⟩ := minimizing_support_nonzero_point hn hE hv
  have hn0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  refine ⟨((3:ℝ)/2/‖x‖) • x,
    (isCone_perimeterSupport hE.1 hc _ (div_pos (by norm_num) hn0) x).mpr hx, ?_⟩
  rw [norm_smul, Real.norm_of_nonneg (div_nonneg (by norm_num) hn0.le), div_mul_cancel₀ _ hn0.ne']

lemma annularFrameMeasure_ne_zero {n : ℕ} (hn : 1 < n) {E : Set (Euc n)}
    (hE : IsLocallyPerimeterMinimizing E) (hc : IsCone E)
    (hv : (0 : Euc n) ∈ perimeterSupport E) : annularFrameMeasure E ≠ 0 := by
  obtain ⟨y, hy, hyn⟩ := cone_support_annular_point hn hE hc hv
  have hyp : 0 < annularWeight y := annularWeight_pos (by rw [hyn]; norm_num) (by rw [hyn]; norm_num)
  have hyb : y ∈ Metric.ball (0 : Euc n) 3 := by simp [Metric.mem_ball, hyn]
  let U := {x : Euc n | 0 < annularWeight x}
  have hU : IsOpen U := isOpen_lt continuous_const annularWeight_continuous
  have hy' : y ∈ (perimeterMeasure E).support := by rwa [perimeterMeasure_support]
  have hp : 0 < perimeterMeasure E (U ∩ Metric.ball 0 3) :=
    (Measure.mem_support_iff_forall y).mp hy' _ ((hU.inter Metric.isOpen_ball).mem_nhds ⟨hyp,hyb⟩)
  intro hz
  have hzae : (fun x : Euc n ↦ (annularWeightNN x : ℝ≥0∞)) =ᵐ[
      (perimeterMeasure E).restrict (Metric.ball 0 3)] 0 :=
    (withDensity_eq_zero_iff annularWeightNN_measurable.coe_nnreal_ennreal.aemeasurable).mp hz
  have hU0 : (perimeterMeasure E).restrict (Metric.ball 0 3) U = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hzae] with x hx
    intro hxp
    have hw0 : annularWeight x = 0 := by
      have hh : annularWeightNN x = 0 := ENNReal.coe_eq_zero.mp hx
      exact congrArg (fun z : ℝ≥0 ↦ (z : ℝ)) hh
    exact (ne_of_gt hxp) hw0
  rw [Measure.restrict_apply hU.measurableSet] at hU0
  exact hp.ne' hU0

lemma annularLink_ne_zero {n : ℕ} (hn : 1 < n) {E : Set (Euc n)}
    (hE : IsLocallyPerimeterMinimizing E) (hc : IsCone E)
    (hv : (0 : Euc n) ∈ perimeterSupport E) : annularLink E ≠ 0 := by
  intro hz
  apply annularFrameMeasure_ne_zero hn hE hc hv
  exact (Measure.map_eq_zero_iff (frameOf_measurable hE.1).aemeasurable).mp hz

lemma annularLink_radial_support {n : ℕ} (hn : 1 < n) {E : Set (Euc n)}
    (hE : IsLocallyPerimeterMinimizing E) (hc : IsCone E) :
    ∀ᵐ e ∂annularLink E, e.1 ∈ perimeterSupport E ∧ ‖e.1‖ = 1 := by
  have hs : ∀ᵐ x ∂perimeterMeasure E, x ∈ perimeterSupport E := by
    rw [← perimeterMeasure_support]
    exact (perimeterMeasure E).support_mem_ae
  have hf := annularLink_frames hn hE hc
  have hr : ∀ᵐ e ∂annularLink E, e.1 ∈ perimeterSupport E := by
    rw [annularLink, ae_map_iff (frameOf_measurable hE.1).aemeasurable
      ((isClosed_perimeterSupport E).preimage continuous_fst).measurableSet,
      annularFrameMeasure, ae_withDensity_iff annularWeightNN_measurable.coe_nnreal_ennreal]
    filter_upwards [ae_restrict_of_ae hs] with x hx hρ
    have hx0 : x ≠ 0 := by
      intro hh
      apply hρ
      apply ENNReal.coe_eq_zero.mpr
      apply Subtype.ext
      simp [hh, annularWeightNN, annularWeight]
    exact (isCone_perimeterSupport hE.1 hc _ (inv_pos.mpr (norm_pos_iff.mpr hx0)) x).mpr hx
  filter_upwards [hr,hf] with e he hframe
  exact ⟨he,hframe.1⟩

end SphericalFrankel
end RPISingularHarnack

end

end OAI
