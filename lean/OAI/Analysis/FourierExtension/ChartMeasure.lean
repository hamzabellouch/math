import Mathlib
import OAI.Analysis.FourierExtension.L2Fourier

namespace OAI

/-! Surface-area measure bounds in graph coordinates. -/

open MeasureTheory
open scoped NNReal ENNReal ContDiff
noncomputable section
open Filter
open scoped Topology ContDiff
open MeasureTheory Set
open scoped ContDiff FourierTransform InnerProductSpace ENNReal
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology
open Set Filter
open scoped ENNReal InnerProductSpace
open scoped FourierTransform SchwartzMap ENNReal
open scoped ENNReal FourierTransform InnerProductSpace
open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal

open MeasureTheory Set
open scoped ENNReal NNReal
namespace DiagonalExtension.ChartMeasure
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]

def dimensionFactor (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)] : ℝ≥0 :=
  Measure.addHaarScalarFactor (Measure.hausdorffMeasure (Module.finrank ℝ E) : Measure E) (volume : Measure E)

lemma hausdorff_eq (hd : Module.finrank ℝ E = 2) :
    (Measure.hausdorffMeasure 2 : Measure E) = dimensionFactor E • volume := by
  simpa [dimensionFactor,hd] using
    (Measure.isAddLeftInvariant_eq_smul
      (Measure.hausdorffMeasure (Module.finrank ℝ E) : Measure E) volume)

omit [NormedSpace ℝ Y] in
theorem coordinate_measure_le {Γ : E → Y} {π : Y → E} {K : Set E} {L κ : ℝ≥0}
    (hd : Module.finrank ℝ E = 2) (hπ : Measurable π)
    (hleft : ∀ x ∈ K, π (Γ x) = x) (hLip : LipschitzOnWith L Γ K) :
    Measure.map π (((κ : ℝ≥0∞) • (Measure.hausdorffMeasure 2 : Measure Y)).restrict (Γ '' K)) ≤
      ((κ : ℝ≥0∞) * (L : ℝ≥0∞)^2 * (dimensionFactor E : ℝ≥0∞)) • volume.restrict K := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.map_apply hπ hB,Measure.restrict_apply (hπ hB)]
  have he : π ⁻¹' B ∩ Γ '' K = Γ '' (B ∩ K) := by
    ext y
    constructor
    · rintro ⟨hy, x,hx,rfl⟩
      exact ⟨x,⟨by simpa only [mem_preimage,hleft x hx] using hy,hx⟩,rfl⟩
    · rintro ⟨x,⟨hxB,hxK⟩,rfl⟩
      exact ⟨by simpa only [mem_preimage,hleft x hxK] using hxB,⟨x,hxK,rfl⟩⟩
  rw [he,Measure.smul_apply]
  have hH := (hLip.mono (show B ∩ K ⊆ K from inter_subset_right)).hausdorffMeasure_image_le
    (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ ≤ (κ : ℝ≥0∞) * ((L : ℝ≥0∞)^2 * (Measure.hausdorffMeasure 2 : Measure E) (B ∩ K)) := by
      simpa only [ENNReal.rpow_two, smul_eq_mul] using mul_le_mul_right hH (κ : ℝ≥0∞)
    _ = _ := by
      rw [hausdorff_eq hd,Measure.smul_apply,Measure.smul_apply,Measure.restrict_apply hB]
      simp only [smul_eq_mul,ENNReal.smul_def]
      ring

end DiagonalExtension.ChartMeasure

namespace DiagonalExtension.ChartMeasure
open MeasureTheory Set
open scoped ENNReal NNReal
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]

omit [NormedSpace ℝ Y] in
theorem exists_graph_density {Γ : E → Y} {π : Y → E} {K : Set E} {L κ : ℝ≥0}
    (hd : Module.finrank ℝ E = 2) (hΓ : Continuous Γ) (hπ : Measurable π)
    (hleft : ∀ x ∈ K, π (Γ x) = x) (hLip : LipschitzOnWith L Γ K)
    (hK : IsCompact K) {μ : Measure Y}
    (hμ : μ ≤ ((κ : ℝ≥0∞) • (Measure.hausdorffMeasure 2 : Measure Y)).restrict (Γ '' K))
    {f : Y → ℂ} (hf : MemLp f 2 μ) :
    ∃ g : E → ℂ, MemLp g 2 volume ∧ HasCompactSupport g ∧ Integrable g volume ∧
      eLpNorm g 2 volume ≤
        ((κ : ℝ≥0∞) * (L : ℝ≥0∞)^2 * (dimensionFactor E : ℝ≥0∞)) ^ (1/2 : ℝ) *
          eLpNorm f 2 μ ∧
      ∀ v : Y → ℂ, Continuous v → (∃ M : ℝ, ∀ y, ‖v y‖ ≤ M) →
        (∫ x, g x * v (Γ x)) = ∫ y, f y * v y ∂μ := by
  classical
  let C : ℝ≥0∞ := (κ : ℝ≥0∞) * (L : ℝ≥0∞)^2 * (dimensionFactor E : ℝ≥0∞)
  have hC : C ≠ (⊤ : ℝ≥0∞) := by dsimp [C]; finiteness
  have hcoord : Measure.map π μ ≤ C • volume :=
    ((Measure.map_mono hμ hπ).trans (coordinate_measure_le hd hπ hleft hLip)).trans
      (by
        intro B
        simp only [Measure.smul_apply, smul_eq_mul]
        exact mul_le_mul_right (Measure.restrict_le_self B) C)
  have hsupport : ∀ᵐ y ∂μ, y ∈ Γ '' K := by
    exact (ae_mono hμ) (ae_restrict_mem (hK.image hΓ).measurableSet)
  let F := hf.toLp f
  have hF : (F : Y → ℂ) =ᵐ[μ] f := MemLp.coeFn_toLp hf
  obtain ⟨u,huInt,huNorm,huSupp,huPair⟩ :=
    BoundedPullback.exists_integrable_density hπ hC hcoord F hK.measurableSet
      hK.measure_lt_top (by
        filter_upwards [hsupport] with y hy
        obtain ⟨x,hx,rfl⟩ := hy
        simp [hleft x hx,hx])
  let g := K.indicator (u : E → ℂ)
  have hgue : g =ᵐ[volume] u := by
    filter_upwards [huSupp] with x hx
    by_cases h : x ∈ K
    · simp [g,h]
    · simp [g,h,hx h]
  have hg : MemLp g 2 volume := (Lp.memLp u).ae_eq hgue.symm
  have hgc : HasCompactSupport g := hK.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (Set.support_indicator_subset) hK.isClosed)
  refine ⟨g,hg,hgc,huInt.congr hgue.symm,?_,?_⟩
  · rw [eLpNorm_congr_ae hgue, ← Lp.enorm_def]
    rw [← ofReal_norm]
    calc
      _ ≤ ENNReal.ofReal (C.toReal ^ (1 / 2 : ℝ) * ‖F‖) := ENNReal.ofReal_le_ofReal huNorm
      _ = C ^ (1/2 : ℝ) * ENNReal.ofReal ‖F‖ := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg _),
          ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num), ENNReal.ofReal_toReal hC]
      _ = _ := by rw [ofReal_norm, Lp.enorm_def, eLpNorm_congr_ae hF]
  · intro v hv hvB
    obtain ⟨M,hM⟩ := hvB
    let w := K.indicator (fun x => v (Γ x))
    have hw : MemLp w 2 volume := by
      rw [memLp_indicator_iff_restrict hK.measurableSet]
      have : IsFiniteMeasure ((volume : Measure E).restrict K) :=
        ⟨by simpa using hK.measure_lt_top⟩
      exact MemLp.of_bound (hv.comp hΓ).aestronglyMeasurable M
        (Filter.Eventually.of_forall (fun x => hM (Γ x)))
    calc
      (∫ x, g x * v (Γ x)) = ∫ x, u x * w x := by
        apply integral_congr_ae
        filter_upwards [huSupp] with x hx
        by_cases h : x ∈ K <;> simp [g,w,h,hx]
      _ = ∫ y, F y * w (π y) ∂μ := huPair w hw
      _ = ∫ y, f y * v y ∂μ := by
        apply integral_congr_ae
        filter_upwards [hF,hsupport] with y hy hs
        obtain ⟨x,hx,rfl⟩ := hs
        simp [hy,w,hleft x hx,hx]

end DiagonalExtension.ChartMeasure

end

end OAI
