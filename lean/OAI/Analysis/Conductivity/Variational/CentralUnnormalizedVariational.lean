import Mathlib
import OAI.Analysis.Conductivity.Sobolev.CentralPhysicalVariational
import OAI.Analysis.Conductivity.Sources.CentralWeightedVariational

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

def angularArea : ℝ := (2*Real.pi)^2

lemma angularArea_ge_one : 1≤angularArea := by
  have hp := Real.pi_gt_three
  dsimp only [angularArea]
  nlinarith [sq_nonneg (Real.pi-3)]

theorem central_unnormalized_variational_exists (s slopes : Fin 3 → ℝ)
    (hs : ∑ i,slopes i=0) :
    ∃ p : centralEnergySpace s,centralM s p=0 ∧
      (∀ v : centralEnergySpace s,
        inner ℝ (centralD s p) (centralD s v)+
          angularArea*(∑ i : Fin 3,inner ℝ (spectralGraphWeight (torusRate s) (centralT s i p))
            (spectralGraphWeight (torusRate s) (centralT s i v)))=
          angularArea*(∑ i : Fin 3,slopes i*spectralGraphMean (torusRate s) (centralT s i v))) ∧
      (∀ q : centralEnergySpace s,(∀ v : centralEnergySpace s,
        inner ℝ (centralD s q) (centralD s v)+
          angularArea*(∑ i : Fin 3,inner ℝ (spectralGraphWeight (torusRate s) (centralT s i q))
            (spectralGraphWeight (torusRate s) (centralT s i v)))=
          angularArea*(∑ i : Fin 3,slopes i*spectralGraphMean (torusRate s) (centralT s i v))) →
        q-p=centralM s q • centralOne s) := by
  exact @central_variational_exists_graph_weighted (centralEnergySpace s) CentralGradients
    inferInstance (centralEnergy_inner s) inferInstance inferInstance inferInstance
    TorusModes inferInstance angularArea angularArea_ge_one (torusRate s) (centralD s) (centralT s)
    (centralM s) (centralOne s)
    (centralAmbientM_one s) (centralAmbientD_one s) (centralAmbientWeight_one s)
    (centralOne_mean s) (centralCoercivityConstant s) (centralCoercivityConstant_pos s)
    (central_graph_coercivity s) slopes hs

end ScalarConductivity

end

end OAI
