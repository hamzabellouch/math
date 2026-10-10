import OAI.Geometry.RCD.Metric.BoundedTimeAverageIntegral

namespace OAI

/-! # Uniform control of averaged endpoint pairings -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem time_average_pairing_error
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (H : ℝ → X → ℝ) (hH : Measurable (Function.uncurry H))
    {Ω : Set X} (hΩ : IsCompact Ω) {a b h t : ℝ} {L : ℝ≥0}
    (hL : LipschitzOnWith L (Function.uncurry H) (Ioo a b ×ˢ Ω))
    (e : Y → X) (he : Measurable e) (hs : ∀ᵐ y ∂ν, e y ∈ Ω)
    (hh : 0 < h) (ha : a < t-h) (hb : t+h < b) :
    |(∫ y, timeIntervalAverage (fun q => H q (e y)) h t ∂ν) -
      (∫ y, H t (e y) ∂ν)| ≤ ν.real univ*((L:ℝ)*h) := by
  have ht : t ∈ Ioo a b := ⟨by linarith,by linarith⟩
  have hc : ContinuousOn (H t) Ω :=
    hL.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => ⟨ht,hx⟩)
  obtain ⟨M,hM⟩ := hΩ.exists_bound_of_continuousOn hc
  have hf : StronglyMeasurable (fun p : ℝ × Y => H p.1 (e p.2)) :=
    (hH.comp (measurable_fst.prodMk (he.comp measurable_snd))).stronglyMeasurable
  have hf0 : AEStronglyMeasurable (fun y => H t (e y)) ν :=
    (hH.comp (measurable_const.prodMk he)).aestronglyMeasurable
  have hi0 : Integrable (fun y => H t (e y)) ν :=
    Integrable.of_bound hf0 M (hs.mono fun y hy => hM (e y) hy)
  have hinc (q : ℝ) (hq : q ∈ Icc (t-h) (t+h)) (x : X) (hx : x ∈ Ω) :
      |H q x-H t x| ≤ (L:ℝ)*h := by
    have hd := hL.dist_le_mul (q,x) ⟨⟨ha.trans_le hq.1,hq.2.trans_lt hb⟩,hx⟩ (t,x) ⟨ht,hx⟩
    simp only [Function.uncurry,Prod.dist_eq,dist_self,Real.dist_eq,max_eq_left (abs_nonneg (q-t))] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left
      (abs_le.mpr ⟨by linarith [hq.1],by linarith [hq.2]⟩) L.coe_nonneg)
  have hbound : ∀ᵐ y ∂ν, ∀ q ∈ Icc (t-h) (t+h), |H q (e y)| ≤ (L:ℝ)*h+M := by
    filter_upwards [hs] with y hy q hq
    calc
      _ ≤ |H q (e y)-H t (e y)|+|H t (e y)| := by
        simpa only [sub_add_cancel] using abs_add_le (H q (e y)-H t (e y)) (H t (e y))
      _ ≤ _ := add_le_add (hinc q hq (e y) hy) (by simpa only [Real.norm_eq_abs] using hM (e y) hy)
  have hiavg := bounded_time_average_integrable ν (fun q y => H q (e y)) hf hh hbound
  rw [← integral_sub hiavg hi0]
  calc
    _ ≤ ∫ y, |timeIntervalAverage (fun q => H q (e y)) h t-H t (e y)| ∂ν :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _ : Y, (L:ℝ)*h ∂ν :=
      integral_mono_ae (hiavg.sub hi0).abs (integrable_const _)
        (hs.mono fun y hy => timeIntervalAverage_local_lipschitz_error H hL hh ha hb hy)
    _ = _ := by rw [integral_const,smul_eq_mul]

end RegularPointCoordinates

end

end OAI
