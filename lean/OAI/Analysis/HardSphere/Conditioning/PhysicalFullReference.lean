import Mathlib
import OAI.Analysis.HardSphere.Conditioning.PhysicalObservation
import OAI.Analysis.HardSphere.Allocation.PhysicalMidpointReference

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {D W V : Type*} [MeasurableSpace D] [MeasurableSpace W] [MeasurableSpace V]

lemma compProd_prod_const (μ : Measure D) [SFinite μ] (κ : Kernel D W) [IsSFiniteKernel κ]
    (η : Measure V) [SFinite η] :
    (μ.compProd (κ ×ₖ Kernel.const D η)).map MeasurableEquiv.prodAssoc.symm =
      (μ.compProd κ).prod η := by
  have he : κ ×ₖ Kernel.const D η=κ ⊗ₖ Kernel.const (D×W) η := by
    ext d s hs
    rw [Kernel.prod_apply,Measure.prod_apply hs,Kernel.compProd_apply hs]
    rfl
  rw [he,Measure.compProd_assoc,Measure.compProd_const]
end HardSphere.Comparison
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma physicalFullMidpoint_split {N K M G : ℕ} {L : Length}
    (g : Fin G) (a : GridAllocation N K (G*M)) (d : PhysicalDatum N K M G L)
    (w : {i // i∈groupUnion g a}→C(Time,Point)) (e : C(Time,Point)) :
    physicalFullMidpoint (Function.Embedding.subtype (fun i ↦ i∈groupUnion g a))
      (d,(MeasurableEquiv.piOptionEquivProd (fun _ : Option {i // i∈groupUnion g a} ↦ C(Time,Point))).symm (w,e)) =
    fun i ↦ i.elim (projectPoint L (e midpointTime))
      (physicalRecoveredMidpoint g a (d,projectGroup w)) := by
  let p := Function.Embedding.subtype (fun i ↦ i∈groupUnion g a)
  funext i
  cases i with
  | none =>
    change fillGroup p _ _ (optionParticle p none)=_
    rw [fillGroup_selected]
    rfl
  | some i =>
    by_cases hi : i∈groupUnion g a
    · change fillGroup p _ _ (optionParticle p (some ⟨i,hi⟩))=_
      rw [fillGroup_selected]
      simp only [Option.elim_some,physicalRecoveredMidpoint,physicalRecoveredPath,dite_eq_left hi]
      rfl
    · have hn : some i∉Set.range (optionParticle p) := by
        rintro ⟨j,hj⟩
        cases j with
        | none => cases hj
        | some j => exact hi ((Option.some.inj hj) ▸ j.property)
      unfold physicalFullMidpoint fillGroup
      rw [Function.extend_apply' _ _ _ hn]
      simp only [Option.elim_some,physicalRecoveredMidpoint,physicalRecoveredPath,dite_eq_right hi]

theorem physicalPrimary_joint_split {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (μ : Measure (PhysicalDatum N K M G L)) [SFinite μ]
    (g : Fin G) (a : GridAllocation N K (G*M)) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (v : Fin 3→Fin K) :
    μ.compProd (physicalPrimaryReference hL g m t r R C S u
      (fun i : {i // i∈groupUnion g a} ↦ i.val) v)=
    ((μ.compProd (datumGroupReference hL g a m r R C S t u)).prod (cellPathReference v)).map
      (fun z ↦ (z.1.1,(MeasurableEquiv.piOptionEquivProd
        (fun _ : Option {i // i∈groupUnion g a} ↦ C(Time,Point))).symm (z.1.2,z.2))) := by
  let e := (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option {i // i∈groupUnion g a} ↦ C(Time,Point))).symm
  have he : physicalPrimaryReference hL g m t r R C S u
      (fun i : {i // i∈groupUnion g a} ↦ i.val) v =
      ((datumGroupReference hL g a m r R C S t u) ×ₖ Kernel.const _ (cellPathReference v)).map e := by
    ext d : 1
    rw [physicalPrimaryReference_actual,Kernel.map_apply _ e.measurable,Kernel.prod_apply,Kernel.const_apply]
  rw [he,Measure.compProd_map e.measurable]
  rw [←compProd_prod_const μ (datumGroupReference hL g a m r R C S t u) (cellPathReference v),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem physicalBranch_full_midpoint_raw {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time) (v : Fin 3→Fin K) :
    ((physicalBranchLaw hL μ g b a m r R C S s₀ (2*t) u).compProd
      (physicalPrimaryReference hL g m t r R C S u
        (fun i : {i // i∈groupUnion g a} ↦ i.val) v)).map
          (fun z ↦ (z.1,physicalFullMidpoint (Function.Embedding.subtype
            (fun i ↦ i∈groupUnion g a)) z)) =
    ((rawPhysicalBranch hL μ g b a m r R C S s₀ (2*t) u).prod (cellPathReference v)).map
      (fun z ↦ (physicalDatum g m r R C S s₀ u (labelBridgePath N L (2*t) z.1,a),
        fun i ↦ i.elim (projectPoint L (z.2 midpointTime))
          (labelBridgePath N L (2*t) z.1 midpointTime))) := by
  let f := fun z : (PhysicalDatum N K M G L×Configuration N L)×C(Time,Point) ↦
    (z.1.1,fun i : Option (Fin N) ↦ i.elim (projectPoint L (z.2 midpointTime)) z.1.2)
  have hf : Measurable f := by
    apply measurable_fst.fst.prodMk
    apply Measurable.of_eval
    intro i
    cases i with
    | none =>
      exact (projectPoint_continuous L).measurable.comp
        ((continuous_eval_const midpointTime).measurable.comp measurable_snd)
    | some i => exact (measurable_pi_apply i).comp measurable_fst.snd
  have hg : Measurable (fun z : PhysicalDatum N K M G L×({i // i∈groupUnion g a}→C(Time,Point)) ↦
      (z.1,physicalRecoveredMidpoint g a (z.1,projectGroup z.2))) :=
    measurable_fst.prodMk ((physicalRecoveredMidpoint_measurable g a).comp
      (measurable_fst.prodMk (projectGroup_measurable.comp measurable_snd)))
  have hr : Measurable (fun z : BridgeEndpoints N L×(Fin N→Bridge.Noise) ↦
      (physicalDatum g m r R C S s₀ u (labelBridgePath N L (2*t) z,a),
        labelBridgePath N L (2*t) z midpointTime)) :=
    ((physicalDatum_measurable g m r R C S s₀ u).comp
      ((labelBridgePath_measurable N L (2*t)).prodMk measurable_const)).prodMk
        ((continuous_eval_const midpointTime).measurable.comp (labelBridgePath_measurable N L (2*t)))
  have H := congrArg (fun ν ↦ (ν.prod (cellPathReference v)).map f)
    (physicalBranch_midpoint_raw hL hK h50 μ g b a m r R C S s₀ t u)
  have fix (η : Measure C(Time,Point)) : η.map id=η := Measure.map_id
  conv_lhs at H => rw [←fix (cellPathReference v),Measure.map_prod_map _ _ hg measurable_id]
  conv_rhs at H => rw [←fix (cellPathReference v),Measure.map_prod_map _ _ hr measurable_id]
  rw [Measure.map_map hf (hg.prodMap measurable_id),Measure.map_map hf (hr.prodMap measurable_id)] at H
  rw [physicalPrimary_joint_split,Measure.map_map
    (measurable_fst.prodMk (physicalFullMidpoint_measurable _)) (by fun_prop)]
  convert H using 1
  · apply Measure.map_congr
    filter_upwards [] with z
    simp only [Function.comp_def,Prod.map,Function.id_def,f,physicalFullMidpoint_split]
  · rfl

end HardSphere.Groups
end
end

end OAI
