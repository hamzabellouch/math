import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafNormalizationInjectivity

namespace OAI

/-! # Removing the projective scalar after changing a leaf's origin -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem anchorNormalize_eq_of_basedRealMeasure_eq
    (ν ρ : Measure ℝ) [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure ρ]
    (J : Set ℝ) (t : ℝ)
    (hνt : 0 < ν (Metric.ball t 1)) (hρt : 0 < ρ (Metric.ball t 1))
    (h : basedRealMeasure ν t = basedRealMeasure ρ t) :
    anchorNormalize ν J = anchorNormalize ρ J := by
  let e := Homeomorph.subRight t
  have H := congrArg (fun η : Measure ℝ => anchorNormalize η (e '' J)) h
  change anchorNormalize (anchorNormalize (centerRealMeasure ν t) (Metric.ball 0 1)) (e '' J) =
    anchorNormalize (anchorNormalize (centerRealMeasure ρ t) (Metric.ball 0 1)) (e '' J) at H
  rw [anchorNormalize_twice _ _ _
      (by rw [centerRealMeasure_ball]; exact hνt.ne')
      (by rw [centerRealMeasure_ball]; exact measure_ball_lt_top.ne),
    anchorNormalize_twice _ _ _
      (by rw [centerRealMeasure_ball]; exact hρt.ne')
      (by rw [centerRealMeasure_ball]; exact measure_ball_lt_top.ne)] at H
  change anchorNormalize (ν.map e.toMeasurableEquiv) (e.toMeasurableEquiv '' J) =
    anchorNormalize (ρ.map e.toMeasurableEquiv) (e.toMeasurableEquiv '' J) at H
  rw [anchorNormalize_map_equiv ν e.toMeasurableEquiv,
    anchorNormalize_map_equiv ρ e.toMeasurableEquiv] at H
  exact e.measurableEmbedding.map_injective H

theorem anchorNormalize_eq_of_rebasedRealMeasure_eq
    (ν ρ : Measure ℝ) [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure ρ]
    (J : Set ℝ) (t u : ℝ)
    (hνt : 0 < ν (Metric.ball t 1)) (hρu : 0 < ρ (Metric.ball u 1))
    (h : basedRealMeasure ρ u = basedRealMeasure (basedRealMeasure ν t) (u-t)) :
    anchorNormalize ν J = anchorNormalize ρ J := by
  have he : basedRealMeasure ρ u = basedRealMeasure ν u := by
    simpa only [basedRealMeasure_rebase ν t (u-t) hνt, add_sub_cancel] using h
  have hνu : 0 < ν (Metric.ball u 1) := by
    by_contra hn
    have hz : ν (Metric.ball u 1) = 0 := le_antisymm (not_lt.mp hn) bot_le
    have hb := congrArg (fun η : Measure ℝ => η (Metric.ball 0 1)) he
    rw [basedRealMeasure_ball_one ρ u hρu] at hb
    have hz' : basedRealMeasure ν u (Metric.ball 0 1) = 0 := by
      change (centerRealMeasure ν u (Metric.ball 0 1))⁻¹ *
        centerRealMeasure ν u (Metric.ball 0 1) = 0
      rw [centerRealMeasure_ball, hz, mul_zero]
    rw [hz'] at hb
    exact one_ne_zero hb
  exact anchorNormalize_eq_of_basedRealMeasure_eq ν ρ J u hνu hρu he.symm

lemma translatedRealMeasure_locallyFinite (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (a : ℝ) :
    IsLocallyFiniteMeasure (ν.map (Homeomorph.addRight a)) := by
  have he : (Homeomorph.addRight a : ℝ → ℝ) = Homeomorph.subRight (-a) := by
    funext x
    change x+a=x-(-a)
    ring
  rw [he]
  exact centerRealMeasure_locallyFinite ν (-a)

lemma translatedRealMeasure_ball (ν : Measure ℝ) (t a r : ℝ) :
    ν.map (Homeomorph.addRight a) (Metric.ball (t+a) r) = ν (Metric.ball t r) := by
  rw [←centerRealMeasure_ball, centerRealMeasure_translate, centerRealMeasure_ball]

theorem anchorNormalize_eq_of_shifted_rebasedRealMeasure_eq
    (ν ρ : Measure ℝ) [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure ρ]
    (J : Set ℝ) (t u a b : ℝ)
    (hνt : 0 < ν (Metric.ball t 1)) (hρu : 0 < ρ (Metric.ball u 1))
    (h : basedRealMeasure ρ u = basedRealMeasure (basedRealMeasure ν t) ((u+b)-(t+a))) :
    anchorNormalize (ν.map (Homeomorph.addRight a)) J =
      anchorNormalize (ρ.map (Homeomorph.addRight b)) J := by
  let : IsLocallyFiniteMeasure (ν.map (Homeomorph.addRight a)) :=
    translatedRealMeasure_locallyFinite ν a
  let : IsLocallyFiniteMeasure (ρ.map (Homeomorph.addRight b)) :=
    translatedRealMeasure_locallyFinite ρ b
  apply anchorNormalize_eq_of_rebasedRealMeasure_eq _ _ J (t+a) (u+b)
  · rwa [translatedRealMeasure_ball]
  · rwa [translatedRealMeasure_ball]
  · simpa only [basedRealMeasure_translate] using h

end DukePrimeDegree

end

end OAI
