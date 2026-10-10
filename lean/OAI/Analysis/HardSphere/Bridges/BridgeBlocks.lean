import Mathlib
import OAI.Analysis.HardSphere.Bridges.GaussianPacking
import OAI.Analysis.HardSphere.Bridges.GroundBridge
import OAI.Analysis.HardSphere.Conditioning.ProductExpose

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere
open Wiener Comparison Bridge

lemma uncurveBridge_preserving (N : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin N) (Fin 3) C(Time,ℝ)).symm
      (Measure.pi fun _ : Fin N ↦ Bridge.law) (coordinateBridge N) := by
  refine ⟨(MeasurableEquiv.curry _ _ _).symm.measurable,?_⟩
  simpa only [Measure.infinitePi_eq_pi,Bridge.law,coordinateBridge] using Measure.infinitePi_map_curry_symm (fun _ : Fin N ↦ fun _ : Fin 3 ↦ bridgeLaw)

instance bridgeEndpointBase_finite (N : ℕ) (L : Length) : IsFiniteMeasure (bridgeEndpointBase N L) := by
  unfold bridgeEndpointBase
  infer_instance

def labelBridgePath (N : ℕ) (L : Length) (t : ℝ) (p : BridgeEndpoints N L×(Fin N→Bridge.Noise)) : ConfigurationPath N L :=
  endpointBridgePath N L t (p.1,fun j ↦ p.2 j.1 j.2)
lemma labelBridgePath_preserving (N : ℕ) (L : Length) (t : ℝ) :
    MeasurePreserving (labelBridgePath N L t) ((bridgeEndpointBase N L).prod (Measure.pi fun _ : Fin N ↦ Bridge.law)) (freePathLaw N L t) :=
  (endpointBridgePath_preserving N L t).comp ((MeasurePreserving.id (bridgeEndpointBase N L)).prod (uncurveBridge_preserving N))
lemma labelBridgePath_measurable (N : ℕ) (L : Length) (t : ℝ) : Measurable (labelBridgePath N L t) :=
  (labelBridgePath_preserving N L t).measurable

instance endpointWeightedBase_sfinite {N : ℕ} {L : Length} (u : Jet N L) (t : ℝ) : SFinite (endpointWeightedBase u t) := by
  unfold endpointWeightedBase bridgeEndpointBase
  infer_instance

def labelInteraction (N : ℕ) (L : Length) (a t : ℝ) : Set (BridgeEndpoints N L×(Fin N→Bridge.Noise)) :=
  labelBridgePath N L t ⁻¹' staysAllowed N L a
lemma labelInteraction_measurable (N : ℕ) (L : Length) (a t : ℝ) : MeasurableSet (labelInteraction N L a t) :=
  (staysAllowed_open N L a).measurableSet.preimage (labelBridgePath_measurable N L t)

lemma genuine_ground_label_bridge {N : ℕ} {L : Length} (u : Jet N L) (a t : ℝ) :
    (((endpointWeightedBase u t).prod (Measure.pi fun _ : Fin N ↦ Bridge.law)).restrict (labelInteraction N L a t)).map (labelBridgePath N L t)=
      groundPathLaw N L a t u := by
  have h := ((MeasurePreserving.id (endpointWeightedBase u t)).prod (uncurveBridge_preserving N)).restrict_preimage
    (endpointInteraction_measurable N L a t)
  have he := congrArg (fun μ : Measure (BridgeEndpoints N L×CoordinatePaths N) ↦ μ.map (endpointBridgePath N L t)) h.map_eq
  rw [Measure.map_map (endpointBridgePath_continuous N L t).measurable h.measurable] at he
  exact he.trans (genuine_ground_bridge u a t)

lemma genuine_ground_exposed {N : ℕ} {L : Length} (u : Jet N L) (a t : ℝ)
    (p : Fin N→Prop) [DecidablePred p] :
    ((exposedLaw (endpointWeightedBase u t) (fun _ : Fin N ↦ Bridge.law) p (labelInteraction N L a t)).compProd
      (fiberNormalize (Kernel.const _ (Measure.pi fun _ : {i // p i} ↦ Bridge.law)) (blockEvent p (labelInteraction N L a t)))).map
      (labelBridgePath N L t ∘ blockGlue p)=groundPathLaw N L a t u := by
  let : SFinite (exposedLaw (endpointWeightedBase u t) (fun _ : Fin N ↦ Bridge.law) p (labelInteraction N L a t)) := by
    unfold exposedLaw
    infer_instance
  rw [←Measure.map_map (labelBridgePath_measurable N L t) (blockGlue_measurable p),exposed_block_reconstruct _ _ _ (labelInteraction_measurable N L a t)]
  exact genuine_ground_label_bridge u a t

end HardSphere

end
end

end

end OAI
