import Mathlib
import OAI.Analysis.HardSphere.Cutoffs.DiameterTail

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener
attribute [local irreducible] torusDistance freeTrajectory

lemma free_diameter_tail {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀ R : ℝ, 0≤R → wiener {w | R≤‖w‖} ≤ M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {L : Length} {h S : ℝ} (hh : 0<h) (hS : 0≤S) (X : Configuration 1 L) :
    coordinateWiener 1 {w | S < intervalDiameter 0 1 (freeTrajectory 1 L h w X)} ≤
      3*M*ENNReal.ofReal (Real.exp (-c*(S/(36*Real.sqrt h))^2)) := by
  have hs : 0<Real.sqrt h := Real.sqrt_pos.mpr hh
  have hp := free_diameterRatio_tail htail hs (le_of_eq (Real.sq_sqrt hh.le).symm)
    (div_nonneg hS hs.le) X
  have he : {w | S < intervalDiameter 0 1 (freeTrajectory 1 L h w X)}=
      {w | S/Real.sqrt h < diameterRatio (Real.sqrt h) (freeTrajectory 1 L h w X)} := by
    ext w
    exact (div_lt_div_iff_of_pos_right hs).symm
  rw [he]
  convert hp using 2
  congr 3
  field_simp

lemma reversed_splitTime {s t : ℝ} (hs : 0<s) (ht : 0<t) :
    reverseTime (splitTime s t hs ht)=splitTime t s ht hs := by
  apply Subtype.ext
  change 1-s/(s+t)=t/(t+s)
  have hh : s+t≠0 := by linarith
  field_simp; ring

end HardSphere.PathCutoff

end
end

end

end OAI
