import OAI.Geometry.RuledCovering.Frames

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def pairPlaneEquiv : (ℝ × ℝ) ≃ᵐ Plane :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

@[simp] lemma pairPlaneEquiv_apply (q : ℝ × ℝ) : pairPlaneEquiv q = vec2 q.1 q.2 := rfl

lemma pairPlane_measurePreserving : MeasurePreserving pairPlaneEquiv volume volume :=
  (PiLp.volume_preserving_toLp (Fin 2)).comp (volume_preserving_finTwoArrow ℝ).symm

lemma plane_integral_pair (f : Plane → ℝ) :
    (∫ z, f z) = ∫ q : ℝ × ℝ, f (vec2 q.1 q.2) :=
  (pairPlane_measurePreserving.integral_comp pairPlaneEquiv.measurableEmbedding f).symm

lemma plane_integrable_pair (f : Plane → ℝ) :
    Integrable (fun q : ℝ × ℝ => f (vec2 q.1 q.2)) ↔ Integrable f :=
  pairPlane_measurePreserving.integrable_comp_emb pairPlaneEquiv.measurableEmbedding

lemma plane_setIntegral_vertical {S : Set Plane} (hS : MeasurableSet S)
    {f : Plane → ℝ} (hf : IntegrableOn f S) :
    (∫ z in S, f z) = ∫ b : ℝ, ∫ r in {r : ℝ | vec2 b r ∈ S}, f (vec2 b r) := by
  rw [← integral_indicator hS,plane_integral_pair]
  rw [Measure.volume_eq_prod,integral_prod _ (by simpa only [Measure.volume_eq_prod] using (plane_integrable_pair _).mpr (hf.integrable_indicator hS))]
  apply integral_congr_ae
  filter_upwards with b
  have hm : MeasurableSet {r : ℝ | vec2 b r ∈ S} := hS.preimage (pairPlaneEquiv.measurable.comp (measurable_const.prodMk measurable_id))
  rw [← integral_indicator hm]
  rfl

lemma plane_setIntegral_horizontal {S : Set Plane} (hS : MeasurableSet S)
    {f : Plane → ℝ} (hf : IntegrableOn f S) :
    (∫ z in S, f z) = ∫ r : ℝ, ∫ b in {b : ℝ | vec2 b r ∈ S}, f (vec2 b r) := by
  rw [← integral_indicator hS,plane_integral_pair]
  rw [Measure.volume_eq_prod,integral_prod_symm _ (by simpa only [Measure.volume_eq_prod] using (plane_integrable_pair _).mpr (hf.integrable_indicator hS))]
  apply integral_congr_ae
  filter_upwards with r
  have hm : MeasurableSet {b : ℝ | vec2 b r ∈ S} := hS.preimage (pairPlaneEquiv.measurable.comp (measurable_id.prodMk measurable_const))
  rw [← integral_indicator hm]
  rfl

lemma plane_setIntegral_vertical_interval {S : Set Plane} (hS : MeasurableSet S)
    {f : Plane → ℝ} (hf : IntegrableOn f S) {s : Set ℝ} (hs : MeasurableSet s)
    {l u : ℝ → ℝ} (heq : ∀ z : Plane, z ∈ S ↔ z 0 ∈ s ∧ z 1 ∈ Icc (l (z 0)) (u (z 0))) :
    (∫ z in S, f z) = ∫ b in s, ∫ r in Icc (l b) (u b), f (vec2 b r) := by
  rw [plane_setIntegral_vertical hS hf,← integral_indicator hs]
  congr 1
  funext b
  by_cases hb : b ∈ s
  · rw [Set.indicator_of_mem hb]
    apply setIntegral_congr_set
    filter_upwards with r
    apply propext
    simpa only [vec2_apply_zero,vec2_apply_one,hb,true_and] using heq (vec2 b r)
  · rw [Set.indicator_of_notMem hb]
    have he : {r : ℝ | vec2 b r ∈ S} = ∅ := by
      ext r
      simpa [hb] using heq (vec2 b r)
    simp [he]

lemma plane_setIntegral_horizontal_interval {S : Set Plane} (hS : MeasurableSet S)
    {f : Plane → ℝ} (hf : IntegrableOn f S) {s : Set ℝ} (hs : MeasurableSet s)
    {l u : ℝ → ℝ} (heq : ∀ z : Plane, z ∈ S ↔ z 1 ∈ s ∧ z 0 ∈ Icc (l (z 1)) (u (z 1))) :
    (∫ z in S, f z) = ∫ r in s, ∫ b in Icc (l r) (u r), f (vec2 b r) := by
  rw [plane_setIntegral_horizontal hS hf,← integral_indicator hs]
  congr 1
  funext r
  by_cases hr : r ∈ s
  · rw [Set.indicator_of_mem hr]
    apply setIntegral_congr_set
    filter_upwards with b
    apply propext
    simpa only [vec2_apply_zero,vec2_apply_one,hr,true_and] using heq (vec2 b r)
  · rw [Set.indicator_of_notMem hr]
    have he : {b : ℝ | vec2 b r ∈ S} = ∅ := by
      ext b
      simpa [hr] using heq (vec2 b r)
    simp [he]

lemma plane_volume_vertical_interval {S : Set Plane} (hS : MeasurableSet S)
    (hfin : volume S ≠ ⊤) {s : Set ℝ} (hs : MeasurableSet s)
    {l u : ℝ → ℝ} (heq : ∀ z : Plane, z ∈ S ↔ z 0 ∈ s ∧ z 1 ∈ Icc (l (z 0)) (u (z 0))) :
    volume.real S = ∫ b in s, max (u b-l b) 0 := by
  have hi := plane_setIntegral_vertical_interval hS (integrableOn_const (C := (1:ℝ)) hfin) hs heq
  simpa [measureReal_def,Real.volume_Icc,ENNReal.toReal_ofReal'] using hi

lemma plane_volume_horizontal_interval {S : Set Plane} (hS : MeasurableSet S)
    (hfin : volume S ≠ ⊤) {s : Set ℝ} (hs : MeasurableSet s)
    {l u : ℝ → ℝ} (heq : ∀ z : Plane, z ∈ S ↔ z 1 ∈ s ∧ z 0 ∈ Icc (l (z 1)) (u (z 1))) :
    volume.real S = ∫ r in s, max (u r-l r) 0 := by
  have hi := plane_setIntegral_horizontal_interval hS (integrableOn_const (C := (1:ℝ)) hfin) hs heq
  simpa [measureReal_def,Real.volume_Icc,ENNReal.toReal_ofReal'] using hi

end RuledApproximation

end

end OAI
