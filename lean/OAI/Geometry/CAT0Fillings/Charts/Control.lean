import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.DenseTests
import OAI.Geometry.CAT0Fillings.Charts.DensityPush

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open MeasureTheory

section BorelChartTests
variable {Z X : Type*} [MeasurableSpace Z] [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
theorem signed_chart_control_borel (μ : Measure Z) (ν : Measure X) [IsFiniteMeasure ν]
    {φ : Z → X} (hφ : Measurable φ) {w : Z → ℝ} (hw : Integrable w μ)
    (hcontrol : ∀ b : X → ℝ, BoundedLip b →
      |∫ z, w z * b (φ z) ∂μ| ≤ ∫ x, |b x| ∂ν)
    {b : X → ℝ} (hb : Measurable b) (hB : ∃ M : ℝ, ∀ x, |b x| ≤ M) :
    |∫ z, w z * b (φ z) ∂μ| ≤ ∫ x, |b x| ∂ν := by
  let τ := densityPush μ φ (fun z => |w z|)
  let : IsFiniteMeasure τ := densityPush_finite μ φ hw.abs
  let η := ν+τ
  have hνη : ν ≤ η := Measure.le_add_right le_rfl
  have hτη : τ ≤ η := Measure.le_add_left le_rfl
  have hbi : Integrable b η := by
    obtain ⟨M,hM⟩ := hB
    exact Integrable.of_bound hb.aestronglyMeasurable M
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hM x)
  obtain ⟨f,hf⟩ := BorelCoefficients.exists_lipschitz_approximation η hbi
  have hfi (j : ℕ) : Integrable ((f j).val) η :=
    (f j).val.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hwb : Integrable (fun z => w z*b (φ z)) μ :=
    integrable_weighted_comp μ hφ hw hb hB
  have hwf (j : ℕ) : Integrable (fun z => w z*(f j).val (φ z)) μ :=
    integrable_weighted_comp μ hφ hw (f j).val.continuous.measurable (f j).property.2
  have hflim : Tendsto (fun j => ∫ z, w z*(f j).val (φ z) ∂μ) atTop
      (𝓝 (∫ z, w z*b (φ z) ∂μ)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun j => dist_nonneg) (fun j => ?_) hf
    rw [Real.dist_eq,←integral_sub (hwf j) hwb]
    calc |∫ z, w z*(f j).val (φ z)-w z*b (φ z) ∂μ| ≤
          ∫ z, |w z| * |(f j).val (φ z)-b (φ z)| ∂μ := by
            simpa only [←mul_sub,Real.norm_eq_abs,abs_mul] using
              norm_integral_le_integral_norm
                (fun z => w z*(f j).val (φ z)-w z*b (φ z))
      _ = ∫ x, |(f j).val x-b x| ∂τ :=
          (integral_densityPush_measurable μ hφ hw.abs
            (Eventually.of_forall fun _ => abs_nonneg _)
            ((f j).val.continuous.measurable.sub hb).abs).symm
      _ ≤ ∫ x, |(f j).val x-b x| ∂η :=
          integral_mono_measure hτη (Eventually.of_forall fun _ => abs_nonneg _)
            ((hfi j).sub hbi).abs
  have hib : Integrable b ν := hbi.mono_measure hνη
  have hfint : Tendsto (fun j => ∫ x, |(f j).val x| ∂ν) atTop
      (𝓝 (∫ x, |b x| ∂ν)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun j => dist_nonneg) (fun j => ?_) hf
    rw [Real.dist_eq,←integral_sub ((hfi j).mono_measure hνη).abs hib.abs]
    calc |∫ x, |(f j).val x|-|b x| ∂ν| ≤ ∫ x, abs (|(f j).val x|-|b x|) ∂ν := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (fun x => |(f j).val x|-|b x|)
      _ ≤ ∫ x, |(f j).val x-b x| ∂ν :=
          integral_mono_ae (((hfi j).mono_measure hνη).abs.sub hib.abs).abs
            (((hfi j).mono_measure hνη).sub hib).abs
            (Eventually.of_forall fun x => abs_abs_sub_abs_le _ _)
      _ ≤ ∫ x, |(f j).val x-b x| ∂η :=
          integral_mono_measure hνη (Eventually.of_forall fun _ => abs_nonneg _)
            ((hfi j).sub hbi).abs
  exact le_of_tendsto_of_tendsto hflim.abs hfint
    (Eventually.of_forall fun j => hcontrol _ (f j).property)
end BorelChartTests
end CAT0Fillings

namespace CAT0Fillings
open MeasureTheory Set

variable {Z X : Type*} [MeasurableSpace Z] [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

lemma signed_chart_control_dominates_of_measurable
    (μ : Measure Z) (ν : Measure X) [IsFiniteMeasure ν]
    {φ : Z → X} (hφ : MeasurableEmbedding φ) {w : Z → ℝ}
    (hwm : Measurable w) (hw : Integrable w μ)
    (hcontrol : ∀ b : X → ℝ, BoundedLip b →
      |∫ z, w z * b (φ z) ∂μ| ≤ ∫ x, |b x| ∂ν) :
    densityPush μ φ (fun z => |w z|) ≤ ν := by
  classical
  let τ := densityPush μ φ (fun z => |w z|)
  let : IsFiniteMeasure τ := densityPush_finite μ φ hw.abs
  let σ : Z → ℝ := fun z => if w z < 0 then -1 else 1
  have hσm : Measurable σ :=
    Measurable.piecewise (measurableSet_lt hwm measurable_const) measurable_const measurable_const
  have hσabs (z : Z) : |σ z| = 1 := by simp [σ]; split <;> norm_num
  have hσmul (z : Z) : w z * σ z = |w z| := by
    by_cases hz : w z < 0
    · simp [σ,hz,abs_of_neg hz]
    · simp [σ,hz,abs_of_nonneg (le_of_not_gt hz)]
  let σe : X → ℝ := Function.extend φ σ (fun _ => 0)
  have hσem : Measurable σe := hφ.measurable_extend hσm measurable_const
  have hσee (z : Z) : σe (φ z) = σ z := hφ.injective.extend_apply σ (fun _ => 0) z
  have hσeb (x : X) : |σe x| ≤ 1 := by
    by_cases hx : ∃ z, φ z = x
    · obtain ⟨z,rfl⟩ := hx
      rw [hσee,hσabs]
    · rw [show σe x = 0 from Function.extend_apply' σ (fun _ => 0) x hx]
      norm_num
  apply Measure.le_iff.mpr
  intro s hs
  let b := s.indicator σe
  have hbm : Measurable b := hσem.indicator hs
  have hbb (x : X) : |b x| ≤ s.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ s
    · simpa only [b,indicator_of_mem hx] using hσeb x
    · simp [b,hx]
  have hB : ∃ M : ℝ, ∀ x, |b x| ≤ M := ⟨1,fun x => (hbb x).trans (by
    by_cases hx : x ∈ s <;> simp [hx])⟩
  have hbi : Integrable b ν := Integrable.of_bound hbm.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using (hbb x).trans (by by_cases hx : x ∈ s <;> simp [hx]))
  have heq : (∫ z, w z*b (φ z) ∂μ) = τ.real s := by
    rw [←integral_indicator_one hs]
    rw [show τ = densityPush μ φ (fun z => |w z|) from rfl,
      integral_densityPush_measurable μ hφ.measurable hw.abs
        (Eventually.of_forall fun _ => abs_nonneg _)
        (b := s.indicator (1 : X → ℝ)) ((measurable_one : Measurable (1 : X → ℝ)).indicator hs)]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    by_cases hz : φ z ∈ s
    · simpa only [b,indicator_of_mem hz,Pi.one_apply,mul_one,hσee] using hσmul z
    · simp [b,hz]
  have hc := signed_chart_control_borel μ ν hφ.measurable hw hcontrol hbm hB
  rw [heq,abs_of_nonneg (show 0 ≤ τ.real s from ENNReal.toReal_nonneg)] at hc
  have hupper : (∫ x, |b x| ∂ν) ≤ ν.real s := by
    rw [←integral_indicator_one hs]
    exact integral_mono_ae hbi.abs ((integrable_const (1 : ℝ)).indicator hs)
      (Eventually.of_forall hbb)
  exact (ENNReal.toReal_le_toReal (measure_ne_top τ s) (measure_ne_top ν s)).mp
    (hc.trans hupper)

lemma signed_chart_control_dominates_on_of_measurable
    (μ : Measure Z) (ν : Measure X) [IsFiniteMeasure ν]
    {φ : Z → X} (hφ : Measurable φ) {s₀ : Set Z}
    (hμ : ∀ᵐ z ∂μ, z ∈ s₀)
    (he : MeasurableEmbedding (fun z : s₀ => φ (z : Z))) {w : Z → ℝ}
    (hwm : Measurable w) (hw : Integrable w μ)
    (hcontrol : ∀ b : X → ℝ, BoundedLip b →
      |∫ z, w z * b (φ z) ∂μ| ≤ ∫ x, |b x| ∂ν) :
    densityPush μ φ (fun z => |w z|) ≤ ν := by
  classical
  let τ := densityPush μ φ (fun z => |w z|)
  let : IsFiniteMeasure τ := densityPush_finite μ φ hw.abs
  let σ : Z → ℝ := fun z => if w z < 0 then -1 else 1
  have hσm : Measurable σ :=
    Measurable.piecewise (measurableSet_lt hwm measurable_const) measurable_const measurable_const
  have hσabs (z : Z) : |σ z| = 1 := by simp [σ]; split <;> norm_num
  have hσmul (z : Z) : w z * σ z = |w z| := by
    by_cases hz : w z < 0
    · simp [σ,hz,abs_of_neg hz]
    · simp [σ,hz,abs_of_nonneg (le_of_not_gt hz)]
  let σe : X → ℝ := Function.extend (fun z : s₀ => φ (z : Z)) (fun z : s₀ => σ (z : Z)) (fun _ => 0)
  have hσem : Measurable σe := he.measurable_extend (hσm.comp measurable_subtype_coe) measurable_const
  have hσee (z : Z) (hz : z ∈ s₀) : σe (φ z) = σ z :=
    he.injective.extend_apply (fun z : s₀ => σ (z : Z)) (fun _ => 0) ⟨z,hz⟩
  have hσeb (x : X) : |σe x| ≤ 1 := by
    by_cases hx : ∃ z : s₀, φ (z : Z) = x
    · obtain ⟨z,rfl⟩ := hx
      rw [hσee z z.property,hσabs]
    · rw [show σe x = 0 from Function.extend_apply' (fun z : s₀ => σ (z : Z)) (fun _ => 0) x hx]
      norm_num
  apply Measure.le_iff.mpr
  intro s hs
  let b := s.indicator σe
  have hbm : Measurable b := hσem.indicator hs
  have hbb (x : X) : |b x| ≤ s.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ s
    · simpa only [b,indicator_of_mem hx] using hσeb x
    · simp [b,hx]
  have hB : ∃ M : ℝ, ∀ x, |b x| ≤ M := ⟨1,fun x => (hbb x).trans (by
    by_cases hx : x ∈ s <;> simp [hx])⟩
  have hbi : Integrable b ν := Integrable.of_bound hbm.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using (hbb x).trans (by by_cases hx : x ∈ s <;> simp [hx]))
  have heq : (∫ z, w z*b (φ z) ∂μ) = τ.real s := by
    rw [←integral_indicator_one hs]
    rw [show τ = densityPush μ φ (fun z => |w z|) from rfl,
      integral_densityPush_measurable μ hφ hw.abs
        (Eventually.of_forall fun _ => abs_nonneg _)
        (b := s.indicator (1 : X → ℝ)) ((measurable_one : Measurable (1 : X → ℝ)).indicator hs)]
    apply integral_congr_ae
    filter_upwards [hμ] with z hzs
    by_cases hz : φ z ∈ s
    · simpa only [b,indicator_of_mem hz,Pi.one_apply,mul_one,hσee z hzs] using hσmul z
    · simp [b,hz]
  have hc := signed_chart_control_borel μ ν hφ hw hcontrol hbm hB
  rw [heq,abs_of_nonneg (show 0 ≤ τ.real s from ENNReal.toReal_nonneg)] at hc
  have hupper : (∫ x, |b x| ∂ν) ≤ ν.real s := by
    rw [←integral_indicator_one hs]
    exact integral_mono_ae hbi.abs ((integrable_const (1 : ℝ)).indicator hs)
      (Eventually.of_forall hbb)
  exact (ENNReal.toReal_le_toReal (measure_ne_top τ s) (measure_ne_top ν s)).mp
    (hc.trans hupper)

end CAT0Fillings
end

end OAI
