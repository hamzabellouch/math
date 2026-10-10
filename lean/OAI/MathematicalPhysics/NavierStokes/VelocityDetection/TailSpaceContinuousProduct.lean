import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailSpaceIntegrableCompatible

namespace OAI

noncomputable section
namespace VelocityDetection.TailSpace.Jets
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology

theorem continuous_product {n a : ℕ} :
    Continuous (fun p : compatibleJets n a × compatibleJets n a => product p.1 p.2) := by
  have hc : Continuous (fun p : compatibleJets n a × compatibleJets n a => productL n a p.1) :=
    (productL n a).continuous.comp continuous_fst
  exact hc.clm_apply continuous_snd

end VelocityDetection.TailSpace.Jets
end

end OAI
