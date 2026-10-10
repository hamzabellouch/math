import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicJetsCalculus

namespace OAI

noncomputable section
namespace VelocityDetection.PeriodicSpace.Jets
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ZeroAtInfty BigOperators

theorem continuous_product {n a : ℕ} :
    Continuous (fun p : compatibleJets n a × compatibleJets n a => product p.1 p.2) := by
  have hc : Continuous (fun p : compatibleJets n a × compatibleJets n a => productL n a p.1) :=
    (productL n a).continuous.comp continuous_fst
  exact hc.clm_apply continuous_snd

end VelocityDetection.PeriodicSpace.Jets
end

end OAI
