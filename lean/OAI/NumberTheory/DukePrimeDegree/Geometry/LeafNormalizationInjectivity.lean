import OAI.NumberTheory.DukePrimeDegree.Geometry.RootStableHolonomy

namespace OAI

/-!
# Recovering normalized leaf measures from based leaves

Two leaf measures normalized on the same window agree if their based
normalizations agree at one center of positive finite mass. This removes
the projective scalar when applying intrinsic holonomy inside a box.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem eq_of_anchorNormalize_eq {T : Type*} [MeasurableSpace T]
    (ν ρ : Measure T) (S J : Set T) (hνS : ν S = 1) (hρS : ρ S = 1)
    (hνJ : ν J ≠ 0) (hνJfin : ν J ≠ ∞) (hρJ : ρ J ≠ 0) (hρJfin : ρ J ≠ ∞)
    (h : anchorNormalize ν J = anchorNormalize ρ J) : ν = ρ := by
  have he := congrArg (fun η : Measure T => anchorNormalize η S) h
  rw [anchorNormalize_twice ν S J hνJ hνJfin,
    anchorNormalize_twice ρ S J hρJ hρJfin] at he
  simpa only [anchorNormalize, hνS, hρS, inv_one, one_smul] using he

theorem eq_of_basedRealMeasure_eq
    (ν ρ : Measure ℝ) [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure ρ]
    (S : Set ℝ) (hνS : ν S = 1) (hρS : ρ S = 1) (t : ℝ)
    (hνt : 0 < ν (Metric.ball t 1)) (hρt : 0 < ρ (Metric.ball t 1))
    (h : basedRealMeasure ν t = basedRealMeasure ρ t) : ν = ρ := by
  let e := Homeomorph.subRight t
  have hν : centerRealMeasure ν t (e '' S) = 1 := by
    rw [centerRealMeasure, e.isOpenEmbedding.measurableEmbedding.map_apply,
      e.injective.preimage_image]
    exact hνS
  have hρ : centerRealMeasure ρ t (e '' S) = 1 := by
    rw [centerRealMeasure, e.isOpenEmbedding.measurableEmbedding.map_apply,
      e.injective.preimage_image]
    exact hρS
  have he : centerRealMeasure ν t = centerRealMeasure ρ t :=
    eq_of_anchorNormalize_eq _ _ (e '' S) (Metric.ball 0 1) hν hρ
      (by rw [centerRealMeasure_ball]; exact hνt.ne')
      (by rw [centerRealMeasure_ball]; exact measure_ball_lt_top.ne)
      (by rw [centerRealMeasure_ball]; exact hρt.ne')
      (by rw [centerRealMeasure_ball]; exact measure_ball_lt_top.ne) h
  exact e.isOpenEmbedding.measurableEmbedding.map_injective he

/-- Holonomy may compare two different centers. Normalizing both original
measures on the same window still removes the projective scalar. -/
theorem eq_of_rebasedRealMeasure_eq
    (ν ρ : Measure ℝ) [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure ρ]
    (S : Set ℝ) (hνS : ν S = 1) (hρS : ρ S = 1) (t u : ℝ)
    (hνt : 0 < ν (Metric.ball t 1)) (hρu : 0 < ρ (Metric.ball u 1))
    (h : basedRealMeasure ρ u = basedRealMeasure (basedRealMeasure ν t) (u - t)) :
    ν = ρ := by
  have he : basedRealMeasure ρ u = basedRealMeasure ν u := by
    simpa only [basedRealMeasure_rebase ν t (u - t) hνt,
      add_sub_cancel] using h
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
  exact eq_of_basedRealMeasure_eq ν ρ S hνS hρS u hνu hρu he.symm

end DukePrimeDegree

end

end OAI
