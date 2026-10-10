import Mathlib
import OAI.Analysis.HardSphere.Bridges.BridgeStrongRegular
import OAI.Analysis.HardSphere.Bridges.BridgeBlocks

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere
open Wiener Bridge GaussianPacking

def labelStartLift {N : ℕ} {L : Length} (e : BridgeEndpoints N L) (i : Fin N) : Point :=
  representative N L e.2 i

def labelEndLift {N : ℕ} {L : Length} (t : ℝ) (e : BridgeEndpoints N L) (i : Fin N) : Point :=
  fun j ↦ labelStartLift e i j+Real.sqrt (2*t)*e.1 (i,j)

lemma labelBridgePath_lift {N : ℕ} {L : Length} (t : ℝ)
    (e : BridgeEndpoints N L) (β : Fin N→Bridge.Noise) (i : Fin N) :
    onePathAt i (labelBridgePath N L t (e,β))=
      projectCurve L (leg t (labelStartLift e i) (labelEndLift t e i) (β i)) := by
  ext s k j
  have hp := congrFun (congrFun (project_representative N L e.2) i) j
  change e.2 i j+((Real.sqrt (2*t)*(e.1 (i,j)*(s:ℝ)+β i j s):ℝ):AddCircle L.val)=
    (((1-(s:ℝ))*labelStartLift e i j+(s:ℝ)*labelEndLift t e i j+Real.sqrt (2*t)*β i j s:ℝ):AddCircle L.val)
  change ((labelStartLift e i j:ℝ):AddCircle L.val)=e.2 i j at hp
  rw [←hp,←QuotientAddGroup.mk_add]
  congr 1
  unfold labelEndLift
  ring

lemma labelBridgePath_one_law {N : ℕ} {L : Length} (t : ℝ)
    (e : BridgeEndpoints N L) (i : Fin N) :
    (Measure.pi fun _ : Fin N ↦ Bridge.law).map
      (fun β ↦ onePathAt i (labelBridgePath N L t (e,β)))=
      (Bridge.law.map (leg t (labelStartLift e i) (labelEndLift t e i))).map (projectCurve L) := by
  simp_rw [labelBridgePath_lift]
  have h := congrArg (fun μ : Measure Bridge.Noise ↦ μ.map
    (projectCurve L ∘ leg t (labelStartLift e i) (labelEndLift t e i)))
    (measurePreserving_eval (fun _ : Fin N ↦ Bridge.law) i).map_eq
  rw [Measure.map_map ((projectCurve_continuous L).measurable.comp (leg_continuous t _ _).measurable) (measurable_pi_apply i)] at h
  rw [Measure.map_map (projectCurve_continuous L).measurable (leg_continuous _ _ _).measurable]
  exact h

end HardSphere

end
end

end

end OAI
