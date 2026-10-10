import OAI.NumberTheory.DukePrimeDegree.Geometry.NormalizedProductRectangle

namespace OAI

/-! # Rebasing a normalized real window at its sampled time -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

lemma realWindow_rebase (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (t : ℝ) (ht : 0 < ν (Metric.ball t 1)) (J : Set ℝ) (hJ : MeasurableSet J) :
    ((anchorNormalize ν J).restrict J).map (Homeomorph.subRight t) =
      (anchorNormalize (basedRealMeasure ν t) (Homeomorph.subRight t '' J)).restrict
        (Homeomorph.subRight t '' J) := by
  let E := (Homeomorph.subRight t).toMeasurableEquiv
  have hEJ : MeasurableSet (E '' J) := E.measurableEmbedding.measurableSet_image.mpr hJ
  have h0 : centerRealMeasure ν t (Metric.ball 0 1) ≠ 0 := by
    rw [centerRealMeasure_ball]
    exact ht.ne'
  have htop : centerRealMeasure ν t (Metric.ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  change ((anchorNormalize ν J).restrict J).map E =
    (anchorNormalize (anchorNormalize (centerRealMeasure ν t) (Metric.ball 0 1))
      (E '' J)).restrict (E '' J)
  rw [anchorNormalize_twice _ _ _ h0 htop]
  have hn := anchorNormalize_map_equiv ν E J
  change ((anchorNormalize ν J).restrict J).map E =
    (anchorNormalize (ν.map E) (E '' J)).restrict (E '' J)
  rw [hn,Measure.restrict_map E.measurable hEJ,E.injective.preimage_image]

lemma realWindow_rebase_addRight (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (t : ℝ) (ht : 0 < ν (Metric.ball t 1)) (J : Set ℝ) (hJ : MeasurableSet J) :
    ((anchorNormalize ν J).restrict J).map (Homeomorph.addRight (-t)) =
      (anchorNormalize (basedRealMeasure ν t) (Homeomorph.addRight (-t) '' J)).restrict
        (Homeomorph.addRight (-t) '' J) := by
  have he : (Homeomorph.addRight (-t) : ℝ → ℝ) = Homeomorph.subRight t := by
    funext x
    exact (sub_eq_add_neg x t).symm
  simpa only [he] using realWindow_rebase ν t ht J hJ

end DukePrimeDegree

end

end OAI
