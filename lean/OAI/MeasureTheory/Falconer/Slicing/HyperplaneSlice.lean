import OAI.MeasureTheory.Falconer.Slicing.SlabSliceAverage
import OAI.MeasureTheory.Falconer.Fourier.CoordinateIntegral
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Actual hyperplane slices are bounded by the measurable thin-slab majorant. -/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem lintegral_interval_rescale {r : ℝ} (hr : 0 < r)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ t in Icc (-1 : ℝ) 1, g (r*t)) =
      (ENNReal.ofReal r)⁻¹ * ∫⁻ u in Icc (-r) r, g u := by
  have heq : (fun t : ℝ => (Icc (-r) r).indicator g (r • t)) =
      (Icc (-1 : ℝ) 1).indicator (fun t => g (r*t)) := by
    funext t
    have hm : r*t ∈ Icc (-r) r ↔ t ∈ Icc (-1 : ℝ) 1 := by
      simp only [mem_Icc]
      constructor <;> intro h
      · constructor <;> nlinarith [h.1, h.2]
      · constructor <;> nlinarith [h.1, h.2]
    simp only [indicator, smul_eq_mul, hm]
  have hm : Measurable ((Icc (-r) r).indicator g) := hg.indicator measurableSet_Icc
  have h := lintegral_map (μ := (volume : Measure ℝ)) hm (measurable_const_smul r)
  rw [Measure.map_addHaar_smul volume hr.ne', lintegral_smul_measure] at h
  rw [heq, lintegral_indicator measurableSet_Icc,
    lintegral_indicator measurableSet_Icc] at h
  simpa [Module.finrank_self, abs_of_pos hr, ENNReal.ofReal_inv_of_pos hr] using h.symm

theorem coordinate_slab_average {n : ℕ} {r : ℝ} (hr : 0 < r)
    {F : Space (n+1) → ℝ≥0∞} (hF : Measurable F) :
    (ENNReal.ofReal (2*r))⁻¹ *
        (∫⁻ z : Space (n+1), {z : Space (n+1) | |z 0| ≤ r}.indicator F z) =
      ∫⁻ y : Space n, ∫⁻ t in Icc (-1 : ℝ) 1,
        (2 : ℝ≥0∞)⁻¹ * F (coordinateJoin y (r*t)) := by
  have hj : Measurable (fun p : Space n × ℝ => coordinateJoin p.1 p.2) :=
    (coordinateEquiv n).symm.measurable
  have hc (y : Space n) : Measurable (fun t : ℝ => F (coordinateJoin y t)) :=
    hF.comp (hj.comp (measurable_const.prodMk measurable_id))
  have hm : Measurable ({z : Space (n+1) | |z 0| ≤ r}.indicator F) :=
    hF.indicator (measurableSet_le (by fun_prop) measurable_const)
  rw [← (coordinateEquiv_measurePreserving n).symm.lintegral_comp hm]
  change (ENNReal.ofReal (2*r))⁻¹ *
    (∫⁻ p : Space n × ℝ, {z : Space (n+1) | |z 0| ≤ r}.indicator F
      (coordinateJoin p.1 p.2) ∂volume.prod volume) = _
  have hprod := lintegral_prod
    (fun p : Space n × ℝ => {z : Space (n+1) | |z 0| ≤ r}.indicator F
      (coordinateJoin p.1 p.2))
    (show AEMeasurable (fun p : Space n × ℝ =>
      {z : Space (n+1) | |z 0| ≤ r}.indicator F (coordinateJoin p.1 p.2))
      (volume.prod volume) from (hm.comp hj).aemeasurable)
  rw [hprod]
  have hi (y : Space n) :
      (∫⁻ t : ℝ, {z : Space (n+1) | |z 0| ≤ r}.indicator F (coordinateJoin y t)) =
        ∫⁻ t in Icc (-r) r, F (coordinateJoin y t) := by
    rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro t
    simp [indicator, coordinateJoin_eq, abs_le]
  have hs (y : Space n) : (∫⁻ t in Icc (-r) r, F (coordinateJoin y t)) =
      ENNReal.ofReal r * ∫⁻ t in Icc (-1 : ℝ) 1, F (coordinateJoin y (r*t)) := by
    rw [lintegral_interval_rescale hr (hc y), ← mul_assoc,
      ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top, one_mul]
  simp_rw [hi, hs]
  rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr
    (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : 0 < 2*r)))]
  apply lintegral_congr
  intro y
  rw [lintegral_const_mul' _ _ (by simp)]
  have hscalar : (ENNReal.ofReal (2*r))⁻¹ * ENNReal.ofReal r = (2 : ℝ≥0∞)⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity : 0 < 2*r),
      ← ENNReal.ofReal_mul (by positivity)]
    have he : (2*r)⁻¹*r = (2 : ℝ)⁻¹ := by field_simp
    rw [he]
    simpa only [ENNReal.ofReal_ofNat] using
      ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)
  rw [← mul_assoc, hscalar]

theorem coordinate_slice_le_slab_liminf {n : ℕ}
    {F : Space (n+1) → ℝ≥0∞} (hF : Continuous F) :
    (∫⁻ y : Space n, F (coordinateJoin y 0)) ≤
      liminf (fun k : ℕ => (ENNReal.ofReal (2*(1/((k : ℝ)+1))))⁻¹ *
        ∫⁻ z : Space (n+1),
          {z : Space (n+1) | |z 0| ≤ 1/((k : ℝ)+1)}.indicator F z) atTop := by
  let H (k : ℕ) (p : Space n × ℝ) : ℝ≥0∞ :=
    (2 : ℝ≥0∞)⁻¹ * F (coordinateJoin p.1 ((1/((k : ℝ)+1))*p.2))
  let ν : Measure (Space n × ℝ) := volume.prod (volume.restrict (Icc (-1 : ℝ) 1))
  have hj : Continuous (fun p : Space n × ℝ => coordinateJoin p.1 p.2) := by
    simp only [coordinateJoin_eq]
    fun_prop
  have hm (k : ℕ) : Measurable (H k) := by
    apply Measurable.const_mul
    exact hF.measurable.comp (hj.measurable.comp
      (measurable_fst.prodMk (measurable_const.mul measurable_snd)))
  have ht (p : Space n × ℝ) :
      Tendsto (fun k : ℕ => H k p) atTop
        (𝓝 ((2 : ℝ≥0∞)⁻¹ * F (coordinateJoin p.1 0))) := by
    have hzero : Tendsto (fun k : ℕ => (1/((k : ℝ)+1))*p.2) atTop (𝓝 (0 : ℝ)) := by
      simpa only [zero_mul] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const p.2
    have hc : Continuous (fun t : ℝ => F (coordinateJoin p.1 t)) :=
      hF.comp (hj.comp (continuous_const.prodMk continuous_id))
    have htest : Continuous (fun t : ℝ => (2 : ℝ≥0∞)⁻¹ * F (coordinateJoin p.1 t)) :=
      (ENNReal.continuous_const_mul (by simp : (2 : ℝ≥0∞)⁻¹ ≠ ∞)).comp hc
    exact (htest.tendsto 0).comp hzero
  have hf := lintegral_liminf_le (μ := ν) (u := (atTop : Filter ℕ)) hm
  simp_rw [(ht _).liminf_eq] at hf
  have hleft : (∫⁻ p, (2 : ℝ≥0∞)⁻¹ * F (coordinateJoin p.1 0) ∂ν) =
      ∫⁻ y : Space n, F (coordinateJoin y 0) := by
    have hmeas : Measurable (fun p : Space n × ℝ =>
        (2 : ℝ≥0∞)⁻¹ * F (coordinateJoin p.1 0)) :=
      ((hF.measurable.comp (hj.measurable.comp
        (measurable_fst.prodMk measurable_const))).const_mul _)
    dsimp only [ν]
    rw [lintegral_prod _ hmeas.aemeasurable]
    apply lintegral_congr
    intro y
    change (∫⁻ _t : ℝ in Icc (-1 : ℝ) 1,
      (2 : ℝ≥0∞)⁻¹ * F (coordinateJoin y 0)) = F (coordinateJoin y 0)
    rw [lintegral_const]
    norm_num only [Measure.restrict_apply_univ, Real.volume_Icc, sub_neg_eq_add,
      one_add_one_eq_two, ENNReal.ofReal_ofNat]
    calc
      _ = ((2 : ℝ≥0∞)⁻¹ * 2) * F (coordinateJoin y 0) := by ac_rfl
      _ = _ := by rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  rw [hleft] at hf
  convert hf using 1
  congr 1
  funext k
  rw [coordinate_slab_average (by positivity) hF.measurable]
  exact (lintegral_prod _ (hm k).aemeasurable).symm

noncomputable def hyperplaneSliceEmbedding {n : ℕ} (w : Sphere (n+1))
    (y : Space n) : Space (n+1) :=
  (northRotation w).symm (coordinateJoin y 0)

theorem hyperplane_slice_le_majorant {n : ℕ} {F : Space (n+1) → ℝ≥0∞}
    (hF : Continuous F) (w : Sphere (n+1)) :
    (∫⁻ y : Space n, F (hyperplaneSliceEmbedding w y)) ≤ slabSliceMajorant F w := by
  let e := northRotation w
  have h := coordinate_slice_le_slab_liminf (hF.comp e.symm.continuous)
  change (∫⁻ y : Space n, (F ∘ e.symm) (coordinateJoin y 0)) ≤ _
  apply h.trans_eq
  apply congrArg (fun f : ℕ → ℝ≥0∞ => liminf f atTop)
  funext k
  congr 1
  have hi (z : Space (n+1)) : inner ℝ (e.symm z) (w : Space (n+1)) = z 0 := by
    rw [← e.inner_map_map, e.apply_symm_apply, northRotation_apply,
      gnomonicChart_zero_coe, inner_northLift_zero]
  have hm : Measurable
      ({z : Space (n+1) | |inner ℝ z (w : Space (n+1))| ≤ 1/((k : ℝ)+1)}.indicator F) :=
    hF.measurable.indicator (measurableSet_le (by fun_prop) measurable_const)
  have hp := e.symm.measurePreserving.lintegral_comp hm
  convert hp using 1
  apply lintegral_congr
  intro z
  simp only [indicator, mem_ofPred_eq, Function.comp_apply, hi]

end Falconer

end OAI
