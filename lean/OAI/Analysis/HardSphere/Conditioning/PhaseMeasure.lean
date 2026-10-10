import Mathlib
import OAI.Analysis.HardSphere.Bridges.BridgeResidual
import OAI.Analysis.HardSphere.Comparison.PiAC

namespace OAI

section

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener

def localLiftBox {N : ℕ} (L : Length) (c : LiftedConfiguration N) : Set (LiftedConfiguration N) :=
  Set.univ.pi (fun i ↦ Set.univ.pi (fun j ↦ Icc (c i j-L.val/2) (c i j+L.val/2)))

lemma localLiftBox_preserving {N : ℕ} (L : Length) (c : LiftedConfiguration N) :
    MeasurePreserving (project N L) (volume.restrict (localLiftBox L c)) volume := by
  have hi (i : Fin N) : MeasurePreserving (fun x : Fin 3 → ℝ ↦ fun j ↦ (x j : AddCircle L.val))
      (volume.restrict (Set.univ.pi (fun j ↦ Icc (c i j-L.val/2) (c i j+L.val/2)))) volume := by
    have hp := measurePreserving_pi (fun j : Fin 3 ↦ volume.restrict (Icc (c i j-L.val/2) (c i j+L.val/2)))
      (fun _ : Fin 3 ↦ (volume : Measure (AddCircle L.val)))
      (f:=fun _ x ↦ (x:AddCircle L.val)) (fun j ↦ ?_)
    · change MeasurePreserving _ ((Measure.pi (fun _ : Fin 3 ↦ (volume : Measure ℝ))).restrict _) (Measure.pi (fun _ : Fin 3 ↦ (volume : Measure (AddCircle L.val))))
      simpa only [Measure.restrict_pi_pi] using hp
    · have hp := AddCircle.measurePreserving_mk L.val (c i j-L.val/2)
      rw [restrict_Ioc_eq_restrict_Icc,show c i j-L.val/2+L.val=c i j+L.val/2 by ring] at hp
      exact hp
  have hp := measurePreserving_pi
    (fun i ↦ volume.restrict (Set.univ.pi (fun j ↦ Icc (c i j-L.val/2) (c i j+L.val/2))))
    (fun _ : Fin N ↦ (volume : Measure (Torus L))) hi
  change MeasurePreserving (fun X : LiftedConfiguration N ↦ fun i j ↦ (X i j : AddCircle L.val)) ((Measure.pi (fun _ : Fin N ↦ (volume : Measure (Fin 3 → ℝ)))).restrict _) (Measure.pi (fun _ : Fin N ↦ (volume : Measure (Torus L))))
  simpa only [project,localLiftBox,Measure.restrict_pi_pi] using hp

lemma ball_subset_localLiftBox {N : ℕ} (L : Length) (c : LiftedConfiguration N) {r : ℝ}
    (hr : r≤L.val/2) : Metric.ball c r ⊆ localLiftBox L c := by
  intro X hX i hi j hj
  have hd : dist (X i j) (c i j)<r :=
    (dist_le_pi_dist _ _ j).trans_lt ((dist_le_pi_dist _ _ i).trans_lt hX)
  rw [Real.dist_eq,abs_lt] at hd
  constructor <;> linarith

lemma gaussianCoordinates_ac (N : ℕ) : gaussianCoordinates N ≪ (volume : Measure (Direction N → ℝ)) :=
  Measure.pi_ac _ _ (fun _ ↦ gaussianReal_absolutelyContinuous 0 (by norm_num))
lemma gaussianCoordinates_ac' (N : ℕ) : (volume : Measure (Direction N → ℝ)) ≪ gaussianCoordinates N :=
  Measure.pi_ac _ _ (fun _ ↦ gaussianReal_absolutelyContinuous' 0 (by norm_num))

def flattenEquiv (N : ℕ) : LiftedConfiguration N ≃L[ℝ] (Direction N → ℝ) :=
  (LinearEquiv.curry ℝ ℝ (Fin N) (Fin 3)).symm.toContinuousLinearEquiv

lemma flatten_quasi (N : ℕ) : QuasiMeasurePreserving (flattenEquiv N)
    (volume : Measure (LiftedConfiguration N)) (volume : Measure (Direction N → ℝ)) := by
  let := (flattenEquiv N).isAddHaarMeasure_map (volume : Measure (LiftedConfiguration N))
  exact ⟨(flattenEquiv N).continuous.measurable,absolutelyContinuous_isAddHaarMeasure _ _⟩

lemma endpointNoise_quasi {N : ℕ} {t : ℝ} (ht : 0<t) (X : LiftedConfiguration N) :
    QuasiMeasurePreserving (fun Y : LiftedConfiguration N ↦
      fun j : Direction N ↦ (Y j.1 j.2-X j.1 j.2)/Real.sqrt (2*t))
      (volume : Measure (LiftedConfiguration N)) (volume : Measure (Direction N → ℝ)) := by
  have ht' : Real.sqrt (2*t) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  have hs := (volume : Measure (LiftedConfiguration N)).quasiMeasurePreserving_smul (inv_ne_zero ht')
  have ha := (measurePreserving_add_right (volume : Measure (LiftedConfiguration N)) (-X)).quasiMeasurePreserving
  convert (flatten_quasi N).comp (hs.comp ha) using 1
  funext Y j
  change (Y j.1 j.2-X j.1 j.2)/Real.sqrt (2*t)=(Real.sqrt (2*t))⁻¹*(Y j.1 j.2+-X j.1 j.2)
  ring

end HardSphere

end
end

end

end OAI
