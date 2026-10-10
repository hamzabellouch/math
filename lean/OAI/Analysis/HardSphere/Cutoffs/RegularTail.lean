import Mathlib
import OAI.Analysis.HardSphere.Cutoffs.PathLift
import OAI.Analysis.HardSphere.Bridges.EndpointTail

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

lemma free_endpoint_regular_tail {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀ R : ℝ, 0≤R → wiener {w | R≤‖w‖} ≤ M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {L : Length} {h t S : ℝ} (hh : 0 < h) (ht : 0<t) (hS : 0≤S) (X : Configuration 1 L) :
    coordinateWiener 1 {w | ¬EndpointRegular (splitTime h t hh ht) S (freeTrajectory 1 L (h+t) w X)} ≤
      2*(3*M*ENNReal.ofReal (Real.exp (-c*(S/(36*Real.sqrt h))^2))) := by
  let p := 3*M*ENNReal.ofReal (Real.exp (-c*(S/(36*Real.sqrt h))^2))
  let E : Set (ConfigurationPath 1 L) := {ω | S < intervalDiameter 0 1 ω}
  have hE : MeasurableSet E := measurableSet_lt measurable_const (intervalDiameter_continuous L 0 1).measurable
  have hp (Y : Configuration 1 L) : coordinateWiener 1 {w | freeTrajectory 1 L h w Y ∈ E} ≤ p :=
    free_diameter_tail htail hh hS Y
  have h₁ := free_prefix_event hh ht hE p hp X
  have h₂ := free_suffix_event ht hh hE p hp X
  have he : {w | ¬EndpointRegular (splitTime h t hh ht) S (freeTrajectory 1 L (h+t) w X)} =
      {w | configurationPrefix 1 L (splitTime h t hh ht) (freeTrajectory 1 L (h+t) w X) ∈ E} ∪
      {w | configurationSuffix 1 L (splitTime t h ht hh) (freeTrajectory 1 L (t+h) w X) ∈ E} := by
    ext w
    change (¬(intervalDiameter 0 (splitTime h t hh ht) _ ≤ S ∧ intervalDiameter (reverseTime (splitTime h t hh ht)) 1 _ ≤ S)) ↔
      (S < intervalDiameter 0 1 (configurationPrefix 1 L (splitTime h t hh ht) (freeTrajectory 1 L (h+t) w X)) ∨
       S < intervalDiameter 0 1 (configurationSuffix 1 L (splitTime t h ht hh) (freeTrajectory 1 L (t+h) w X)))
    rw [not_and_or,not_le,not_le,interval_prefix (splitTime h t hh ht),
      interval_suffix (reverseTime (splitTime h t hh ht)),reversed_splitTime,add_comm t h]
  rw [he]
  exact (measure_union_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

lemma free_regular_tail {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀ R : ℝ, 0≤R → wiener {w | R≤‖w‖} ≤ M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {L : Length} {r τ R h S : ℝ} (hr : 0 < r) (hτ : 0 < τ) (hτr : τ≤r^2) (hR : 0≤R)
    (m : ℕ) (hm : 0 < m) (hh : 0 < h) (hhT : h < (m:ℝ)*τ) (hS : 0≤S) (X : Configuration 1 L) :
    coordinateWiener 1 {w | ¬Regular m r R (meanCost+1)
      (splitTime h ((m:ℝ)*τ-h) hh (sub_pos.mpr hhT)) S (freeTrajectory 1 L ((m:ℝ)*τ) w X)} ≤
      (m:ℝ≥0∞)*(3*M*ENNReal.ofReal (Real.exp (-c*(R/36)^2)))+
      ENNReal.ofReal (Real.exp (-(m:ℝ)/((1+R)^3)))+
      2*(3*M*ENNReal.ofReal (Real.exp (-c*(S/(36*Real.sqrt h))^2))) := by
  have h₁ := free_mesh_regular_tail htail hr hτ hτr hR m hm X
  have h₂ := free_endpoint_regular_tail htail hh (sub_pos.mpr hhT) hS X
  rw [add_sub_cancel] at h₂
  have he : {w | ¬Regular m r R (meanCost+1) (splitTime h ((m:ℝ)*τ-h) hh (sub_pos.mpr hhT)) S (freeTrajectory 1 L ((m:ℝ)*τ) w X)} =
      {w | ¬MeshRegular m r R (meanCost+1) (freeTrajectory 1 L ((m:ℝ)*τ) w X)} ∪
      {w | ¬EndpointRegular (splitTime h ((m:ℝ)*τ-h) hh (sub_pos.mpr hhT)) S (freeTrajectory 1 L ((m:ℝ)*τ) w X)} := by
    ext w
    exact not_and_or
  rw [he]
  exact (measure_union_le _ _).trans (add_le_add h₁ h₂)

end HardSphere.PathCutoff

end
end

end

end OAI
