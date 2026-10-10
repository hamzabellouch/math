import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalBranchLaw

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

def rawPhysicalBranch {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (_group : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ T : ℝ) (u : Time) :=
  ((allocationBase μ (gridAllocationKernel hL (G*M)) b a).prod
    (Measure.pi fun _ : Fin N ↦ Bridge.law)).restrict
      (labelInteraction N L r T∩flagEvent (eligibilityFlag (K:=K) m r R C S s₀ T u) b)
instance rawPhysicalBranch_sfinite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ T : ℝ) (u : Time) :
    SFinite (rawPhysicalBranch hL μ g b a m r R C S s₀ T u) := by
  unfold rawPhysicalBranch; infer_instance

theorem physicalBranch_reference_raw {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time) :
    (physicalBranchLaw hL μ g b a m r R C S s₀ (2*t) u).compProd
      (datumPhysicalReference hL g a m r R C S t u)=
    (rawPhysicalBranch hL μ g b a m r R C S s₀ (2*t) u).map
      (fun z ↦ (physicalDatum g m r R C S s₀ u (labelBridgePath N L (2*t) z,a),
        fun i : {i // i∈groupUnion g a} ↦ onePathAt i (labelBridgePath N L (2*t) z))) := by
  let p := fun i ↦ i∈groupUnion g a
  let B := labelInteraction N L r (2*t)∩
    flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b
  have hB : MeasurableSet B := (labelInteraction_measurable N L r (2*t)).inter
    (flagEvent_measurable _ (fun i ↦ eligibilityFlag_measurable m r R C S s₀ (2*t) u i) b)
  have hm : Measurable (fun z : BridgeEndpoints N L×(Fin N→Bridge.Noise) ↦
      (physicalDatum g m r R C S s₀ u (labelBridgePath N L (2*t) z,a),
        fun i : {i // p i} ↦ onePathAt i (labelBridgePath N L (2*t) z))) :=
    ((physicalDatum_measurable g m r R C S s₀ u).comp
      ((labelBridgePath_measurable N L (2*t)).prodMk measurable_const)).prodMk
        (Measurable.of_eval fun i ↦ (onePathAt_continuous (i:Fin N)).measurable.comp
          (labelBridgePath_measurable N L (2*t)))
  rw [physicalBranchLaw,←actual_physical_branch_joint hL hK h50 μ m r R C S s₀ t u g b a]
  have : SFinite (exposedLaw (allocationBase μ (gridAllocationKernel hL (G*M)) b a)
      (fun _ : Fin N ↦ Bridge.law) p B) := by unfold exposedLaw; infer_instance
  have H := congrArg (fun ν ↦ ν.map (fun z ↦
    (physicalDatum g m r R C S s₀ u (labelBridgePath N L (2*t) z,a),
      fun i : {i // p i} ↦ onePathAt i (labelBridgePath N L (2*t) z))))
    (exposed_block_reconstruct (allocationBase μ (gridAllocationKernel hL (G*M)) b a)
      (fun _ : Fin N ↦ Bridge.law) p hB)
  rw [Measure.map_map hm (blockGlue_measurable p)] at H
  dsimp only [Function.comp_def,rawPhysicalBranch,selectedPhysicalPath,p,B] at H ⊢
  convert H using 1
  congr 20
  all_goals try exact Subsingleton.elim _ _
  funext z
  unfold selectedPhysicalPath
  congr 20
  all_goals first | exact Subsingleton.elim _ _ | (funext index; congr 20)

def physicalRecoveredPath {N K M G : ℕ} {L : Length} (g : Fin G)
    (a : GridAllocation N K (G*M))
    (z : PhysicalDatum N K M G L×({i // i∈groupUnion g a}→ ConfigurationPath 1 L)) :
    Fin N→ ConfigurationPath 1 L :=
  fun i ↦ if hi : i∈groupUnion g a then z.2 ⟨i,hi⟩ else z.1.2.2.2.2 i
lemma physicalRecoveredPath_measurable {N K M G : ℕ} {L : Length} (g : Fin G)
    (a : GridAllocation N K (G*M)) :
    Measurable (physicalRecoveredPath (L:=L) g a) := by
  apply Measurable.of_eval
  intro i
  unfold physicalRecoveredPath
  by_cases hi : i∈groupUnion g a
  · simp only [dite_eq_left hi]
    exact (measurable_pi_apply (⟨i,hi⟩ : {i // i∈groupUnion g a})).comp measurable_snd
  · simp only [dite_eq_right hi]
    exact (datumFrozen_measurable i).comp measurable_fst
lemma physicalRecoveredPath_actual {N K M G : ℕ} {L : Length} (g : Fin G)
    (a : GridAllocation N K (G*M)) (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (F : ConfigurationPath N L) :
    physicalRecoveredPath g a (physicalDatum g m r R C S s₀ u (F,a),fun i ↦ onePathAt i F)=
      fun i ↦ onePathAt i F := by
  funext i
  by_cases hi : i∈groupUnion g a <;> simp [physicalRecoveredPath,physicalDatum,hi]

def physicalRecoveredMidpoint {N K M G : ℕ} {L : Length} (g : Fin G)
    (a : GridAllocation N K (G*M))
    (z : PhysicalDatum N K M G L×({i // i∈groupUnion g a}→ ConfigurationPath 1 L)) : Configuration N L :=
  fun i ↦ physicalRecoveredPath g a z i midpointTime 0
lemma physicalRecoveredMidpoint_measurable {N K M G : ℕ} {L : Length} (g : Fin G)
    (a : GridAllocation N K (G*M)) : Measurable (physicalRecoveredMidpoint (L:=L) g a) :=
  Measurable.of_eval fun i ↦ (measurable_pi_apply 0).comp
    ((continuous_eval_const midpointTime).measurable.comp
      ((measurable_pi_apply i).comp (physicalRecoveredPath_measurable g a)))
lemma physicalRecoveredMidpoint_actual {N K M G : ℕ} {L : Length} (g : Fin G)
    (a : GridAllocation N K (G*M)) (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (F : ConfigurationPath N L) :
    physicalRecoveredMidpoint g a (physicalDatum g m r R C S s₀ u (F,a),fun i ↦ onePathAt i F)=
      F midpointTime := by
  unfold physicalRecoveredMidpoint
  rw [physicalRecoveredPath_actual]
  rfl

theorem physicalBranch_midpoint_raw {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time) :
    ((physicalBranchLaw hL μ g b a m r R C S s₀ (2*t) u).compProd
      (datumGroupReference hL g a m r R C S t u)).map
        (fun z ↦ (z.1,physicalRecoveredMidpoint g a (z.1,projectGroup z.2)))=
    (rawPhysicalBranch hL μ g b a m r R C S s₀ (2*t) u).map
      (fun z ↦ (physicalDatum g m r R C S s₀ u (labelBridgePath N L (2*t) z,a),
        labelBridgePath N L (2*t) z midpointTime)) := by
  have hm := measurable_fst.prodMk (physicalRecoveredMidpoint_measurable (L:=L) g a)
  have H := congrArg (fun ν ↦ ν.map (fun z ↦ (z.1,physicalRecoveredMidpoint g a z)))
    (physicalBranch_reference_raw hL hK h50 μ g b a m r R C S s₀ t u)
  rw [datumPhysicalReference,Measure.compProd_map projectGroup_measurable,
    Measure.map_map hm (measurable_id.prodMap projectGroup_measurable)] at H
  have hr : Measurable (fun z : BridgeEndpoints N L×(Fin N→Bridge.Noise) ↦
      (physicalDatum g m r R C S s₀ u (labelBridgePath N L (2*t) z,a),
        fun i : {i // i∈groupUnion g a} ↦ onePathAt i (labelBridgePath N L (2*t) z))) :=
    ((physicalDatum_measurable g m r R C S s₀ u).comp
      ((labelBridgePath_measurable N L (2*t)).prodMk measurable_const)).prodMk
        (Measurable.of_eval fun i ↦ (onePathAt_continuous (i:Fin N)).measurable.comp
          (labelBridgePath_measurable N L (2*t)))
  rw [Measure.map_map hm hr] at H
  simpa only [Function.comp_def,Prod.map,Function.id_def,physicalRecoveredMidpoint_actual] using H

end HardSphere.Groups
end
end

end OAI
