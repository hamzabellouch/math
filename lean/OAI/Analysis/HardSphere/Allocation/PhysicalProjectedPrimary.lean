import Mathlib
import OAI.Analysis.HardSphere.Conditioning.PhysicalFullReference

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

theorem physicalBranch_primary_midpoint {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time) (v : Fin 3→Fin K) :
    ((physicalBranchLaw hL μ g b a m r R C S s₀ (2*t) u).compProd
      (physicalPrimaryReference hL g m t r R C S u
        (fun i : {i // i∈groupUnion g a} ↦ i.val) v)).map
          (physicalFullMidpoint (Function.Embedding.subtype (fun i ↦ i∈groupUnion g a))) =
    (((rawPhysicalBranch hL μ g b a m r R C S s₀ (2*t) u).map
      (fun z ↦ labelBridgePath N L (2*t) z midpointTime)).prod
      ((cellPathReference v).map (fun e ↦ projectPoint L (e midpointTime)))).map
        (fun z i ↦ i.elim z.2 z.1) := by
  have H := congrArg (fun ν ↦ ν.map Prod.snd)
    (physicalBranch_full_midpoint_raw hL hK h50 μ g b a m r R C S s₀ t u v)
  rw [Measure.map_map measurable_snd
    (measurable_fst.prodMk (physicalFullMidpoint_measurable _)),
    Measure.map_map measurable_snd (by
      apply Measurable.prodMk
      · exact (physicalDatum_measurable g m r R C S s₀ u).comp
          (((labelBridgePath_measurable N L (2*t)).comp measurable_fst).prodMk measurable_const)
      · apply Measurable.of_eval
        intro i
        cases i with
        | none =>
          exact (projectPoint_continuous L).measurable.comp
            ((continuous_eval_const midpointTime).measurable.comp measurable_snd)
        | some i =>
          exact (measurable_pi_apply i).comp
            ((continuous_eval_const midpointTime).measurable.comp
              ((labelBridgePath_measurable N L (2*t)).comp measurable_fst)))] at H
  have hf : Measurable (fun z ↦ labelBridgePath N L (2*t) z midpointTime) :=
    (continuous_eval_const midpointTime).measurable.comp (labelBridgePath_measurable N L (2*t))
  have he : Measurable (fun e : C(Time,Point) ↦ projectPoint L (e midpointTime)) :=
    (projectPoint_continuous L).measurable.comp (continuous_eval_const midpointTime).measurable
  rw [Measure.map_prod_map _ _ hf he,Measure.map_map (by
    apply Measurable.of_eval
    intro i
    cases i with
    | none => exact measurable_snd
    | some i => exact (measurable_pi_apply i).comp measurable_fst) (hf.prodMap he)]
  exact H

end HardSphere.Groups
end
end

end OAI
