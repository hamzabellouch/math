import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.AveragePrecomposeEmbedding

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
lemma take_ofFn_cast {n N : ℕ} (h : n≤N) (seed : Fin N→Bool) :
    (List.ofFn seed).take n=List.ofFn (fun i:Fin n=>seed (Fin.castLE h i)) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_ofFn,min_eq_left h]
  · intro i hi hj
    simp only [List.getElem_take,List.getElem_ofFn]
    rfl
lemma probability_prefix {n N : ℕ} (h : n≤N) (E : (Fin n→Bool)→Prop) :
    probability (fun seed:Fin N→Bool=>E (fun i=>seed (Fin.castLE h i)))=probability E :=
  probability_precompose_embedding ⟨Fin.castLE h,Fin.castLE_injective h⟩ E
end MetricKMedianRecovery.FiniteSampling

end OAI
