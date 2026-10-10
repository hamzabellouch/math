import OAI.Probability.SpanningForest.FiniteUSTIntegrals

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336

def finiteUSTProbability (K : FiniteSubgraphCode)
    (hK : (spanningTrees K).Nonempty) : ProbabilityMeasure EdgeConfiguration :=
  ⟨finiteUSTMeasure K, finiteUSTMeasure_isProbabilityMeasure K hK⟩

@[simp] lemma finiteUSTProbability_toMeasure (K : FiniteSubgraphCode)
    (hK : (spanningTrees K).Nonempty) :
    (finiteUSTProbability K hK : Measure EdgeConfiguration) = finiteUSTMeasure K := rfl

end Problem336

end

end OAI
