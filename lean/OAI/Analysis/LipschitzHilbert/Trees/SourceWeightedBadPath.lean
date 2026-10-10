import OAI.Analysis.LipschitzHilbert.Fourier.LineWeightAverage
import OAI.Analysis.LipschitzHilbert.Trees.SourcePlaneIntegral

namespace OAI

/-! A reference-interval tail estimate retains the complete decaying top
weight. No restriction to the central part of the top is used. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

variable {X : Type*} [MeasurableSpace X]

theorem weighted_small_set_le (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (bad : Set X) (hbad : MeasurableSet bad) {c C δ : ℝ}
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hw : AEStronglyMeasurable w μ)
    (hlo : ∀ᵐ x ∂μ, c ≤ w x) (hhi : ∀ᵐ x ∂μ, w x ≤ C*c)
    (hsmall : μ.real bad ≤ δ*μ.real univ) :
    Integrable (bad.indicator w) μ ∧
      (∫ x, bad.indicator w x ∂μ) ≤ (C*δ)*(∫ x, w x ∂μ) := by
  have hw0 := hlo.mono fun _ hx => hc.trans hx
  have hwi : Integrable w μ := (integrable_const (C*c)).mono' hw (by
    filter_upwards [hw0,hhi] with x hx0 hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg hx0] using hx)
  have hlow : c*μ.real univ ≤ ∫ x, w x ∂μ := by
    simpa only [integral_const,smul_eq_mul,mul_comm] using
      integral_mono_ae (integrable_const c) hwi hlo
  refine ⟨hwi.indicator hbad,?_⟩
  have hupper : (∫ x, bad.indicator w x ∂μ) ≤ C*c*μ.real bad := by
    calc
      _ ≤ ∫ x, bad.indicator (fun _ => C*c) x ∂μ :=
        integral_mono_ae (hwi.indicator hbad) ((integrable_const (C*c)).indicator hbad)
          (hhi.mono fun x hx => by
            by_cases hxb : x ∈ bad
            · simpa only [indicator_of_mem hxb] using hx
            · simp only [indicator_of_notMem hxb,le_refl])
      _ = _ := by rw [integral_indicator hbad,integral_const]; simp [Measure.real,smul_eq_mul,mul_comm]
  calc
    _ ≤ C*c*μ.real bad := hupper
    _ ≤ C*c*(δ*μ.real univ) := mul_le_mul_of_nonneg_left hsmall (mul_nonneg hC hc)
    _ = (C*δ)*(c*μ.real univ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (mul_nonneg hC hδ)

/-- On every interval of top length, an unweighted relative tail becomes
an equally small weighted tail, up to the fixed weight comparison factor. -/
theorem source_line_weighted_bad (T : SlopeBox) (origin y H : ℝ) {K D δ : ℝ}
    (hK : 1 ≤ K) (hD : 0 ≤ D) (hH : 0 < H) (hHT : H ≤ T.length)
    (hδ : 0 ≤ δ) (bad : Set ℝ) (hbad : MeasurableSet bad)
    (hsmall : (volume.restrict (Ico origin (origin+H))).real bad ≤ δ*H) :
    IntegrableOn (bad.indicator (fun x => T.weight K D (x,y+T.slope*x)))
      (Ico origin (origin+H)) volume ∧
      (∫ x in Ico origin (origin+H), bad.indicator
        (fun x => T.weight K D (x,y+T.slope*x)) x) ≤
        (Real.exp (2*D)*δ)*(∫ x in Ico origin (origin+H), T.weight K D (x,y+T.slope*x)) := by
  let μ := volume.restrict (Ico origin (origin+H))
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by simp)
  let c := Real.exp (-D)*T.weight K D (origin,y+T.slope*origin)
  have hc : 0 ≤ c := by
    exact mul_nonneg (Real.exp_pos _).le (T.weight_pos (zero_lt_one.trans_le hK) _ _).le
  apply weighted_small_set_le μ _ bad hbad hc (Real.exp_pos _).le hδ
    (((T.continuous_weight (zero_lt_one.trans_le hK) D).comp (by fun_prop)).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    exact (T.line_weight_comparable origin y x hK hD hHT hx).1
  · filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    apply (T.line_weight_comparable origin y x hK hD hHT hx).2.trans_eq
    dsimp [c]
    rw [← mul_assoc,← Real.exp_add]
    congr 2
    ring
  · have hu : μ.real univ = H := by
      simp only [μ,Measure.real,Measure.restrict_apply_univ,Real.volume_Ico,
        add_sub_cancel_left,ENNReal.toReal_ofReal hH.le]
    rwa [hu]

/-- Summing the line estimates over all tiles and then all tops retains
exactly the total top area and the full spatial weight. -/
theorem source_weighted_bad_path_area {ι : Type*} (tops : Finset ι)
    (T : ι → SlopeBox) (bad : ι → Set (ℝ × ℝ))
    (hbad : ∀ t ∈ tops, MeasurableSet (bad t)) {K D δ : ℝ}
    (hK : 1 ≤ K) (hD : 2 < D) (hδ : 0 ≤ δ)
    (htail : ∀ t ∈ tops, ∀ᵐ y : ℝ ∂volume, ∀ k : ℤ,
      (volume.restrict (sourceLineTile (T t).length k)).real
        {x | (x,y+(T t).slope*x) ∈ bad t} ≤ δ*(T t).length) :
    Integrable (fun z => ∑ t ∈ tops, (bad t).indicator ((T t).weight K D) z)
      (volume.prod volume) ∧
      (∫ z, ∑ t ∈ tops, (bad t).indicator ((T t).weight K D) z ∂volume.prod volume) ≤
        (((Real.exp (2*D)*δ)*(2^D*∫ z, topProfile D z ∂volume.prod volume))*K^2)*
          ∑ t ∈ tops, (T t).length*(T t).width := by
  apply source_plane_finite_area_sum tops T (zero_lt_one.trans_le hK) hD
    (fun t => (T t).slope) (fun t => (T t).length) (fun t _ => (T t).length_pos)
    (Real.exp (2*D)*δ) (fun t => (bad t).indicator ((T t).weight K D))
  · intro t ht
    exact (((T t).continuous_weight (zero_lt_one.trans_le hK) D).measurable.indicator
      (hbad t ht)).aestronglyMeasurable
  · intro t _ z
    exact indicator_nonneg (fun x _ => ((T t).weight_pos (zero_lt_one.trans_le hK) D x).le) z
  · intro t ht
    filter_upwards [htail t ht] with y hy
    intro k
    let B : Set ℝ := {x | (x,y+(T t).slope*x) ∈ bad t}
    have hB : MeasurableSet B := (hbad t ht).preimage (by fun_prop)
    have heq : sourceLineTile (T t).length k =
        Ico ((T t).length*k) ((T t).length*k+(T t).length) := by
      unfold sourceLineTile
      congr 1
      ring
    have hf : (fun x => (bad t).indicator ((T t).weight K D) (x,y+(T t).slope*x)) =
        B.indicator (fun x => (T t).weight K D (x,y+(T t).slope*x)) := by
      funext x
      by_cases hx : (x,y+(T t).slope*x) ∈ bad t
      · simp only [indicator_of_mem hx,indicator_of_mem (show x ∈ B from hx)]
      · simp only [indicator_of_notMem hx,indicator_of_notMem (show x ∉ B from hx)]
    have hb := source_line_weighted_bad (K := K) (D := D) (δ := δ)
      (T t) ((T t).length*k) y (T t).length
      hK (by linarith) (T t).length_pos le_rfl hδ B hB
      (by simpa only [← heq] using hy k)
    simpa only [hf,heq] using hb

end LipschitzHilbert

end

end OAI
