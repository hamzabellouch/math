import OAI.Analysis.IrrationalRotation.Sampling.ProductIdealSamplingOrder

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal
namespace Invariant233.ProductModel.IdealSampling

theorem integral_uniform_displacement (x : Circle) {a : ℝ} (ha : a ≠ 0)
    (f : Circle → ℝ) (hf : Measurable f) :
    (∫ z, f (x + ((a * circleRepresentative z : ℝ) : Circle)) ∂circleMeasure) =
      a⁻¹ * ∫ t in (0 : ℝ)..a, f (x + (t : Circle)) := by
  have hm : Measurable (fun t : ℝ => f (x + ((a * t : ℝ) : Circle))) := by
    apply hf.comp
    fun_prop
  have he := integral_map (μ := circleMeasure)
    Sampling.representative_measurable.aemeasurable hm.aestronglyMeasurable
  rw [Sampling.representative_map_haar] at he
  calc
    _ = ∫ t, f (x + ((a * t : ℝ) : Circle)) ∂volume.restrict (Ico (0 : ℝ) 1) := he.symm
    _ = ∫ t in (0 : ℝ)..1, f (x + ((a * t : ℝ) : Circle)) := by
      rw [restrict_Ico_eq_restrict_Ioc, intervalIntegral.integral_of_le (by norm_num)]
    _ = _ := by
      simpa only [mul_zero, mul_one, smul_eq_mul] using
        (intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
          (fun t : ℝ => f (x + (t : Circle))) ha)

theorem integral_rawKernel_test {h α s : ℝ}
    (hcut : α ≤ ScalarSampling.delta s)
    (ha0 : 0 < h * ScalarSampling.delta s) (ha1 : h * ScalarSampling.delta s ≤ 1)
    (x : Circle) (f : Circle → ℝ) :
    (∫ t in (0 : ℝ)..1, ScalarSampling.rawKernel h α s t * f (x + (t : Circle))) =
      (h * ScalarSampling.delta s)⁻¹ *
        ∫ t in (0 : ℝ)..(h * ScalarSampling.delta s), f (x + (t : Circle)) := by
  let a := h * ScalarSampling.delta s
  have hh : (fun t : ℝ => ScalarSampling.rawKernel h α s t * f (x + (t : Circle))) =
      (Ioo 0 a).indicator (fun t => a⁻¹ * f (x + (t : Circle))) := by
    funext t
    simp only [ScalarSampling.rawKernel, ite_eq_left hcut]
    by_cases ht : t ∈ Ioo 0 a <;> simp [a, Set.indicator, ht] at *
  rw [hh, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]
  have hsub : Ioo (0 : ℝ) a ⊆ Ioc 0 1 := by
    intro t ht
    exact ⟨ht.1, ht.2.le.trans ha1⟩
  rw [inter_eq_left.mpr hsub, restrict_Ioo_eq_restrict_Ioc, integral_const_mul,
    ← intervalIntegral.integral_of_le ha0.le]

theorem integral_displacement_eq_rawKernel {h α : ℝ} (x : Circle)
    (hcut : α ≤ ScalarSampling.delta (circleRepresentative x))
    (ha0 : 0 < h * ScalarSampling.delta (circleRepresentative x))
    (ha1 : h * ScalarSampling.delta (circleRepresentative x) ≤ 1)
    (f : Circle → ℝ) (hf : Measurable f) :
    (∫ z, f (x + ((h * ScalarSampling.delta (circleRepresentative x) *
      circleRepresentative z : ℝ) : Circle)) ∂circleMeasure) =
      ∫ t in (0 : ℝ)..1, ScalarSampling.rawKernel h α (circleRepresentative x) t *
        f (x + (t : Circle)) := by
  rw [integral_uniform_displacement x ha0.ne' f hf,
    integral_rawKernel_test hcut ha0 ha1]

theorem integral_cutoff_displacement_eq_rawKernel {h α : ℝ}
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hα : 0 < α)
    (x : Circle) (f : Circle → ℝ) (hf : Measurable f) :
    (if α ≤ ScalarSampling.delta (circleRepresentative x) then
      ∫ z, f (x + ((h * ScalarSampling.delta (circleRepresentative x) *
        circleRepresentative z : ℝ) : Circle)) ∂circleMeasure else 0) =
      ∫ t in (0 : ℝ)..1, ScalarSampling.rawKernel h α (circleRepresentative x) t *
        f (x + (t : Circle)) := by
  by_cases hcut : α ≤ ScalarSampling.delta (circleRepresentative x)
  · rw [ite_eq_left hcut]
    apply integral_displacement_eq_rawKernel x hcut
      (mul_pos hh0 (hα.trans_le hcut)) _ f hf
    have hx := Sampling.representative_mem_Ico x
    have hd : ScalarSampling.delta (circleRepresentative x) ≤ 1 :=
      (min_le_left _ _).trans hx.2.le
    exact (mul_le_mul_of_nonneg_right hh1 (hα.trans_le hcut).le).trans
      (by simpa using hd)
  · simp only [ite_eq_right hcut, ScalarSampling.rawKernel, zero_mul,
      intervalIntegral.integral_zero]

theorem integral_triangular_endpoint (x : Circle) (f : Circle → ℝ)
    (hf : Measurable f) :
    (∫ z, if circleRepresentative x < circleRepresentative z then f z else 0
      ∂circleMeasure) =
      ∫ y in (circleRepresentative x)..1, f (y : Circle) := by
  let s := circleRepresentative x
  have hx := Sampling.representative_mem_Ico x
  have hm : Measurable (fun y : ℝ => (Ioi s).indicator (fun y => f (y : Circle)) y) := by
    apply Measurable.indicator _ measurableSet_Ioi
    exact hf.comp (by fun_prop)
  have he := integral_map (μ := circleMeasure)
    Sampling.representative_measurable.aemeasurable hm.aestronglyMeasurable
  rw [Sampling.representative_map_haar] at he
  have hcoe (z : Circle) : ((circleRepresentative z : ℝ) : Circle) = z :=
    ProductCocycle.coe_representative z
  calc
    _ = ∫ z, (Ioi s).indicator (fun y => f (y : Circle)) (circleRepresentative z)
        ∂circleMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by simp [Set.indicator, hcoe, s])
    _ = ∫ y, (Ioi s).indicator (fun y => f (y : Circle)) y
        ∂volume.restrict (Ico (0 : ℝ) 1) := he.symm
    _ = ∫ y in s..1, f (y : Circle) := by
      rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
      have hset : Ioi s ∩ Ico (0 : ℝ) 1 = Ioo s 1 := by
        ext y
        constructor
        · intro hy
          exact ⟨hy.1, hy.2.2⟩
        · intro hy
          exact ⟨hy.1, ⟨hx.1.trans hy.1.le, hy.2⟩⟩
      rw [hset, restrict_Ioo_eq_restrict_Ioc, intervalIntegral.integral_of_le hx.2.le]

theorem integral_triangular_endpoint_eq_kernel (x : Circle) (f : Circle → ℝ)
    (hf : Measurable f) :
    (∫ z, if circleRepresentative x < circleRepresentative z then f z else 0
      ∂circleMeasure) =
      ∫ t in (0 : ℝ)..1, ScalarSampling.triangularKernel (circleRepresentative x) t *
        f (x + (t : Circle)) := by
  let s := circleRepresentative x
  have hx := Sampling.representative_mem_Ico x
  have hh : (fun t : ℝ => ScalarSampling.triangularKernel s t * f (x + (t : Circle))) =
      (Ioo 0 (1 - s)).indicator (fun t => f (x + (t : Circle))) := by
    funext t
    simpa only [ScalarSampling.triangularKernel, one_mul] using
      (Set.indicator_mul_left (Ioo 0 (1 - s)) (fun _ : ℝ => (1 : ℝ))
        (fun t => f (x + (t : Circle))) (i := t)).symm
  have hphase : (∫ t in (0 : ℝ)..1,
      ScalarSampling.triangularKernel s t * f (x + (t : Circle))) =
      ∫ t in (0 : ℝ)..(1 - s), f (x + (t : Circle)) := by
    rw [hh, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]
    have hsub : Ioo (0 : ℝ) (1 - s) ⊆ Ioc 0 1 := by
      intro t ht
      exact ⟨ht.1, ht.2.le.trans (by dsimp [s]; linarith [hx.1])⟩
    rw [inter_eq_left.mpr hsub, restrict_Ioo_eq_restrict_Ioc,
      intervalIntegral.integral_of_le (sub_nonneg.mpr hx.2.le)]
  rw [integral_triangular_endpoint x f hf, hphase]
  have hcoe : ((s : ℝ) : Circle) = x := ProductCocycle.coe_representative x
  have he := intervalIntegral.integral_comp_add_left (a := 0) (b := 1 - s)
    (fun y : ℝ => f (y : Circle)) s
  simpa only [AddCircle.coe_add, hcoe, add_zero, add_sub_cancel] using he.symm

end Invariant233.ProductModel.IdealSampling

end

end OAI
