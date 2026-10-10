import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalMixedObservation

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital

lemma point_chart_preserving (L : Length) (c : Point) :
    MeasurePreserving (projectPoint L)
      (volume.restrict (univ.pi (fun j ↦ Icc (c j-L.val/2) (c j+L.val/2)))) volume := by
  have hp (j : Fin 3) : MeasurePreserving (fun value : ℝ ↦ (value : AddCircle L.val))
      (volume.restrict (Icc (c j-L.val/2) (c j+L.val/2))) volume := by
    have hj := AddCircle.measurePreserving_mk L.val (c j-L.val/2)
    rw [restrict_Ioc_eq_restrict_Icc,show c j-L.val/2+L.val=c j+L.val/2 by ring] at hj
    exact hj
  change MeasurePreserving _ ((Measure.pi (fun _ : Fin 3 ↦ (volume : Measure ℝ))).restrict _)
    (Measure.pi (fun _ : Fin 3 ↦ (volume : Measure (AddCircle L.val))))
  simpa only [projectPoint,Measure.restrict_pi_pi] using measurePreserving_pi
    (fun j : Fin 3 ↦ volume.restrict (Icc (c j-L.val/2) (c j+L.val/2)))
    (fun _ : Fin 3 ↦ (volume : Measure (AddCircle L.val))) hp

lemma cellPathReference_midpoint_le {K : ℕ} [NeZero K] {L : Length} (hL : 1≤L.val)
    (v : Fin 3→Fin K) :
    (cellPathReference v).map (fun p ↦ projectPoint L (p midpointTime)) ≤
      volume.restrict (centeredCell L (gridCenter L v)) := by
  let f := fun p : C(Time,Point) ↦ projectPoint L (p midpointTime)
  have hf : Measurable f := (projectPoint_continuous L).measurable.comp
    (continuous_eval_const midpointTime).measurable
  have hs : ∀ᵐx ∂(cellPathReference v).map f,x∈centeredCell L (gridCenter L v) := by
    exact (ae_map_iff hf.aemeasurable (centeredCell_measurable L (gridCenter L v))).mpr
      (cellPathReference_support hL v)
  rw [←Measure.restrict_eq_self_of_ae_mem hs]
  apply Measure.restrict_mono_measure
  rw [cellPathReference,Measure.map_map hf pointAsPath_measurable]
  change (targetUniform (unitTarget (anchorPoint v))).map (projectPoint L)≤volume
  rw [targetUniform,unitTarget_volume,inv_one,one_smul]
  have hsub : unitTarget (anchorPoint v) ⊆
      univ.pi (fun j ↦ Icc (anchorPoint v j-L.val/2) (anchorPoint v j+L.val/2)) := by
    intro x hx j hj
    have h := hx j hj
    constructor <;> linarith [h.1,h.2]
  exact (Measure.map_mono (Measure.restrict_mono_set volume hsub) (projectPoint_continuous L).measurable).trans_eq
    (point_chart_preserving L (anchorPoint v)).map_eq

end HardSphere.Groups
end
end

end OAI
