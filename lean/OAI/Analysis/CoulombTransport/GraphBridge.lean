import OAI.Analysis.CoulombTransport.Model

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356

lemma measurable_tripleFst : Measurable tripleFst := measurable_fst
lemma measurable_tripleSnd : Measurable tripleSnd := measurable_fst.comp measurable_snd
lemma measurable_tripleThd : Measurable tripleThd := measurable_snd.comp measurable_snd

lemma measurable_invDistance : Measurable (fun p : E3 × E3 => invDistance p.1 p.2) := by
  unfold invDistance
  exact ((measurable_fst.sub measurable_snd).norm.ennreal_ofReal).inv

lemma measurable_coulombCost : Measurable coulombCost := by
  unfold coulombCost
  exact ((measurable_invDistance.comp (measurable_tripleFst.prodMk measurable_tripleSnd)).add
    (measurable_invDistance.comp (measurable_tripleFst.prodMk measurable_tripleThd))).add
    (measurable_invDistance.comp (measurable_tripleSnd.prodMk measurable_tripleThd))

def graphMap (T2 T3 : E3 → E3) (x : E3) : Triple := (x, (T2 x, T3 x))

def graphMeasure (mu : Measure E3) (T2 T3 : E3 → E3) : Measure Triple :=
  Measure.map (graphMap T2 T3) mu

lemma measurable_graphMap {T2 T3 : E3 → E3} (h2 : Measurable T2) (h3 : Measurable T3) :
    Measurable (graphMap T2 T3) := measurable_id.prodMk (h2.prodMk h3)

lemma graphMeasure_isThreeCoupling (mu : Measure E3) [IsProbabilityMeasure mu]
    {T2 T3 : E3 → E3} (h2 : Preserves mu T2) (h3 : Preserves mu T3) :
    IsThreeCoupling mu (graphMeasure mu T2 T3) := by
  have hm := measurable_graphMap h2.1 h3.1
  refine ⟨(Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance,
    ?_, ?_, ?_⟩
  · rw [graphMeasure, Measure.map_map measurable_tripleFst hm]
    change Measure.map id mu = mu
    exact Measure.map_id
  · rw [graphMeasure, Measure.map_map measurable_tripleSnd hm]
    exact h2.2
  · rw [graphMeasure, Measure.map_map measurable_tripleThd hm]
    exact h3.2

lemma lintegral_graphMeasure (mu : Measure E3) {T2 T3 : E3 → E3}
    (h2 : Measurable T2) (h3 : Measurable T3) :
    (∫⁻ t, coulombCost t ∂graphMeasure mu T2 T3) = graphCost mu T2 T3 := by
  exact lintegral_map measurable_coulombCost (measurable_graphMap h2 h3)

lemma kantorovichValue_le_graphCost (mu : Measure E3) [IsProbabilityMeasure mu]
    {T2 T3 : E3 → E3} (h2 : Preserves mu T2) (h3 : Preserves mu T3) :
    kantorovichValue mu ≤ graphCost mu T2 T3 := by
  rw [← lintegral_graphMeasure mu h2.1 h3.1]
  exact iInf₂_le (graphMeasure mu T2 T3) (graphMeasure_isThreeCoupling mu h2 h3)

lemma kantorovichValue_le_mongeValue (mu : Measure E3) [IsProbabilityMeasure mu] :
    kantorovichValue mu ≤ mongeValue mu := by
  unfold mongeValue
  exact le_iInf fun T2 => le_iInf fun T3 => le_iInf fun h2 => le_iInf fun h3 =>
    kantorovichValue_le_graphCost mu h2 h3

end Problem356

end

end OAI
