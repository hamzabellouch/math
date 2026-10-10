import Mathlib
import OAI.Geometry.CAT0Fillings.Radial.IntrinsicSlope
import OAI.Geometry.CAT0Fillings.Radial.MetricSlope

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
local instance : MeasurableSpace (Matrix ι ι ℝ) := borel _
local instance : BorelSpace (Matrix ι ι ℝ) := ⟨rfl⟩
lemma measurable_metricSpatialRadialJacobian (t : ℝ) :
    Measurable (fun p : MetricRadialParameters ι =>
      Real.sqrt (metricSpatialRadialForm p.1 p.2.1.1 p.2.1.2 t p.2.2.1 p.2.2.2).det /
        Real.sqrt p.1.det) := by
  apply Measurable.div
  · apply Continuous.measurable
    apply Real.continuous_sqrt.comp
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [metricSpatialRadialForm,Matrix.add_apply,Matrix.sub_apply,
      Matrix.smul_apply,Matrix.vecMulVec_apply,smul_eq_mul]
    fun_prop
  · exact (Real.continuous_sqrt.comp continuous_fst.matrix_det).measurable

theorem integrated_metricSpatialRadialJacobian_hasDerivWithinAt_zero
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : Ω → MetricRadialParameters ι)
    (hp : Measurable p) {B δ : ℝ} (hδ : 0 < δ)
    (hB : ∀ᵐ x ∂μ, ‖p x‖ ≤ B) (hdet : ∀ᵐ x ∂μ, δ ≤ (p x).1.det)
    (hG : ∀ᵐ x ∂μ, (p x).1.PosDef) :
    HasDerivWithinAt
      (fun t => ∫ x, Real.sqrt (metricSpatialRadialForm
        (p x).1 (p x).2.1.1 (p x).2.1.2 t (p x).2.2.1 (p x).2.2.2).det /
          Real.sqrt (p x).1.det ∂μ)
      (∫ x, -((Fintype.card ι : ℝ)*(p x).2.1.1+
        (p x).2.1.2*((p x).2.2.1 ⬝ᵥ ((p x).1)⁻¹.mulVec (p x).2.2.2)) ∂μ)
      (Ici 0) 0 := by
  let J : ℝ → Ω → ℝ := fun t x =>
    Real.sqrt (metricSpatialRadialForm
      (p x).1 (p x).2.1.1 (p x).2.1.2 t (p x).2.2.1 (p x).2.2.2).det /
        Real.sqrt (p x).1.det
  have hJm (t : ℝ) : Measurable (J t) :=
    (measurable_metricSpatialRadialJacobian t).comp hp
  have hJ0 : ∀ᵐ x ∂μ, J 0 x = 1 := by
    filter_upwards [hdet] with x hx
    have hpos : 0 < (p x).1.det := hδ.trans_le hx
    simp [J,metricSpatialRadialForm, (Real.sqrt_pos.2 hpos).ne']
  obtain ⟨C,hC,hbound⟩ := metricSpatialRadialForm_uniform_slope_bound (ι := ι) B δ hδ
  have hJI {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : Integrable (J t) μ := by
    apply (integrable_const (C+1)).mono' (hJm t).aestronglyMeasurable
    filter_upwards [hB,hdet] with x hx hdx
    have he := hbound (p x) hx hdx t ht
    change |J t x-1| ≤ C*t at he
    have hnonneg : 0 ≤ J t x := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.norm_eq_abs,abs_of_nonneg hnonneg]
    have := le_abs_self (J t x-1)
    have hCt : C*t ≤ C := (mul_le_mul_of_nonneg_left ht.2 hC).trans_eq (mul_one C)
    linarith
  have hlim : Tendsto (fun t => ∫ x, (J t x-1)/t ∂μ) (𝓝[>] (0:ℝ))
      (𝓝 (∫ x, -((Fintype.card ι : ℝ)*(p x).2.1.1+
        (p x).2.1.2*((p x).2.2.1 ⬝ᵥ ((p x).1)⁻¹.mulVec (p x).2.2.2)) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    · exact Eventually.of_forall fun t => ((hJm t).sub_const 1 |>.div_const t).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht ht1
      filter_upwards [hB,hdet] with x hx hdx
      simp only [Real.norm_eq_abs,abs_div,abs_of_pos (show 0<t from ht)]
      exact (div_le_iff₀ ht).2 (hbound (p x) hx hdx t ⟨ht.le,ht1.le⟩)
    · exact integrable_const C
    · filter_upwards [hG,hJ0] with x hx hzero
      have hd := (metricSpatialRadialForm_normalized_sqrt_det_hasDerivAt_zero
        (p x).1 (p x).2.1.1 (p x).2.1.2 (p x).2.2.1 (p x).2.2.2 hx).hasDerivWithinAt (s := Ici 0)
      have ht := hasDerivWithinAt_iff_tendsto_slope.mp hd
      have hs : Ici (0:ℝ) \ {0} = Ioi 0 := by simp
      change Tendsto (fun t => slope (fun t => J t x) 0 t) _ _ at ht
      simpa only [hs,slope_def_field,sub_zero,hzero] using ht
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hs : Ici (0:ℝ) \ {0} = Ioi 0 := by simp
  rw [hs]
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht ht1
  rw [slope_def_field,sub_zero]
  change (∫ x, (J t x-1)/t ∂μ) = ((∫ x, J t x ∂μ)-(∫ x, J 0 x ∂μ))/t
  rw [integral_div,integral_sub (hJI ⟨ht.le,ht1.le⟩) (integrable_const 1),
    integral_congr_ae hJ0]

end CAT0Fillings

namespace CAT0Fillings
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

local instance : MeasurableSpace (Matrix ι ι ℝ) := borel _
local instance : BorelSpace (Matrix ι ι ℝ) := ⟨rfl⟩

theorem integrated_intrinsicRadialJacobian_hasDerivWithinAt_zero
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : Ω → MetricRadialParameters ι)
    (hp : Measurable p) {B : ℝ} (hB : 0 ≤ B)
    (hdata : ∀ᵐ x ∂μ, |(p x).2.1.1| ≤ B ∧ |(p x).2.1.2| ≤ B ∧
      (∀ v : ι → ℝ, ((p x).2.2.1 ⬝ᵥ v)^2 ≤ B^2*(v ⬝ᵥ (p x).1.mulVec v)) ∧
      (∀ v : ι → ℝ, ((p x).2.2.2 ⬝ᵥ v)^2 ≤ B^2*(v ⬝ᵥ (p x).1.mulVec v)))
    (hG : ∀ᵐ x ∂μ, (p x).1.PosDef) :
    HasDerivWithinAt
      (fun t => ∫ x, Real.sqrt (metricSpatialRadialForm
        (p x).1 (p x).2.1.1 (p x).2.1.2 t (p x).2.2.1 (p x).2.2.2).det /
          Real.sqrt (p x).1.det ∂μ)
      (∫ x, -((Fintype.card ι : ℝ)*(p x).2.1.1+
        (p x).2.1.2*((p x).2.2.1 ⬝ᵥ ((p x).1)⁻¹.mulVec (p x).2.2.2)) ∂μ)
      (Ici 0) 0 := by
  let J : ℝ → Ω → ℝ := fun t x =>
    Real.sqrt (metricSpatialRadialForm
      (p x).1 (p x).2.1.1 (p x).2.1.2 t (p x).2.2.1 (p x).2.2.2).det /
        Real.sqrt (p x).1.det
  have hJm (t : ℝ) : Measurable (J t) :=
    (measurable_metricSpatialRadialJacobian t).comp hp
  have hJ0 : ∀ᵐ x ∂μ, J 0 x = 1 := by
    filter_upwards [hG] with x hx
    have hpos : 0 < (p x).1.det := hx.det_pos
    simp [J,metricSpatialRadialForm, (Real.sqrt_pos.2 hpos).ne']
  obtain ⟨C,hC,hbound⟩ := metricSpatialRadialForm_intrinsic_uniform_slope_bound (ι := ι) B hB
  have hJI {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : Integrable (J t) μ := by
    apply (integrable_const (C+1)).mono' (hJm t).aestronglyMeasurable
    filter_upwards [hdata,hG] with x hx hgx
    have he := hbound (p x).1 hgx (p x).2.1.1 (p x).2.1.2 hx.1 hx.2.1 (p x).2.2.1 (p x).2.2.2 hx.2.2.1 hx.2.2.2 t ht
    change |J t x-1| ≤ C*t at he
    have hnonneg : 0 ≤ J t x := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.norm_eq_abs,abs_of_nonneg hnonneg]
    have := le_abs_self (J t x-1)
    have hCt : C*t ≤ C := (mul_le_mul_of_nonneg_left ht.2 hC).trans_eq (mul_one C)
    linarith
  have hlim : Tendsto (fun t => ∫ x, (J t x-1)/t ∂μ) (𝓝[>] (0:ℝ))
      (𝓝 (∫ x, -((Fintype.card ι : ℝ)*(p x).2.1.1+
        (p x).2.1.2*((p x).2.2.1 ⬝ᵥ ((p x).1)⁻¹.mulVec (p x).2.2.2)) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    · exact Eventually.of_forall fun t => ((hJm t).sub_const 1 |>.div_const t).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht ht1
      filter_upwards [hdata,hG] with x hx hgx
      simp only [Real.norm_eq_abs,abs_div,abs_of_pos (show 0<t from ht)]
      exact (div_le_iff₀ ht).2 (hbound (p x).1 hgx (p x).2.1.1 (p x).2.1.2 hx.1 hx.2.1 (p x).2.2.1 (p x).2.2.2 hx.2.2.1 hx.2.2.2 t ⟨ht.le,ht1.le⟩)
    · exact integrable_const C
    · filter_upwards [hG,hJ0] with x hx hzero
      have hd := (metricSpatialRadialForm_normalized_sqrt_det_hasDerivAt_zero
        (p x).1 (p x).2.1.1 (p x).2.1.2 (p x).2.2.1 (p x).2.2.2 hx).hasDerivWithinAt (s := Ici 0)
      have ht := hasDerivWithinAt_iff_tendsto_slope.mp hd
      have hs : Ici (0:ℝ) \ {0} = Ioi 0 := by simp
      change Tendsto (fun t => slope (fun t => J t x) 0 t) _ _ at ht
      simpa only [hs,slope_def_field,sub_zero,hzero] using ht
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hs : Ici (0:ℝ) \ {0} = Ioi 0 := by simp
  rw [hs]
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht ht1
  rw [slope_def_field,sub_zero]
  change (∫ x, (J t x-1)/t ∂μ) = ((∫ x, J t x ∂μ)-(∫ x, J 0 x ∂μ))/t
  rw [integral_div,integral_sub (hJI ⟨ht.le,ht1.le⟩) (integrable_const 1),
    integral_congr_ae hJ0]

end CAT0Fillings
namespace CAT0Fillings.IntegerChart
open MeasureTheory Set Filter Metric Matrix
open scoped Topology NNReal Matrix.Norms.Elementwise

variable {X : Type*} [MetricSpace X] [CompactSpace X] {k : ℕ} (C : IntegerChart X k)
local instance : MeasurableSpace (Matrix (Fin k) (Fin k) ℝ) := _root_.borel _
local instance : BorelSpace (Matrix (Fin k) (Fin k) ℝ) := ⟨rfl⟩

end CAT0Fillings.IntegerChart
end
end

end OAI
