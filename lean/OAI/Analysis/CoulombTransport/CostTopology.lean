import OAI.Analysis.CoulombTransport.GraphBridge

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356

lemma invDistance_pos (x y : E3) : 0 < invDistance x y := by
  simp [invDistance]

lemma coulombCost_pos (t : Triple) : 0 < coulombCost t := by
  unfold coulombCost
  exact lt_of_lt_of_le (invDistance_pos _ _)
    ((le_add_right le_rfl).trans (le_add_right le_rfl))

lemma continuous_invDistance : Continuous (fun p : E3 × E3 => invDistance p.1 p.2) := by
  unfold invDistance
  exact (ENNReal.continuous_ofReal.comp (continuous_fst.sub continuous_snd).norm).inv

lemma continuous_coulombCost : Continuous coulombCost := by
  unfold coulombCost
  have h1 : Continuous tripleFst := continuous_fst
  have h2 : Continuous tripleSnd := continuous_fst.comp continuous_snd
  have h3 : Continuous tripleThd := continuous_snd.comp continuous_snd
  exact ((continuous_invDistance.comp (h1.prodMk h2)).add
    (continuous_invDistance.comp (h1.prodMk h3))).add
    (continuous_invDistance.comp (h2.prodMk h3))

lemma lowerSemicontinuous_coulombCost : LowerSemicontinuous coulombCost :=
  continuous_coulombCost.lowerSemicontinuous

lemma graphCost_congr_ae (mu : Measure E3) {T2 T3 S2 S3 : E3 → E3}
    (h2 : T2 =ᵐ[mu] S2) (h3 : T3 =ᵐ[mu] S3) :
    graphCost mu T2 T3 = graphCost mu S2 S3 := by
  apply lintegral_congr_ae
  filter_upwards [h2, h3] with x hx2 hx3
  simp only [hx2, hx3]

lemma graphMeasure_congr_ae (mu : Measure E3) {T2 T3 S2 S3 : E3 → E3}
    (h2 : T2 =ᵐ[mu] S2) (h3 : T3 =ᵐ[mu] S3) :
    graphMeasure mu T2 T3 = graphMeasure mu S2 S3 := by
  apply Measure.map_congr
  filter_upwards [h2, h3] with x hx2 hx3
  simp only [graphMap, hx2, hx3]

end Problem356

end

end OAI
