import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace OAI

/-! Restrict a closed-disk homeomorphism fixing infinity to the punctured disk. -/
noncomputable section
open Set Complex Metric

namespace SLEExactGauge

lemma closedDisk_map_ne_one
    (e : closedBall (0:ℂ) 1 ≃ₜ closedBall (0:ℂ) 1)
    (h1 : e ⟨1,by norm_num⟩=⟨1,by norm_num⟩)
    (z : closedBall (0:ℂ) 1) (hz : (z:ℂ) ≠ 1) : (e z:ℂ) ≠ 1 := by
  intro he
  apply hz
  have hh : e z=e ⟨1,by norm_num⟩ := (Subtype.ext he).trans h1.symm
  exact congrArg Subtype.val (e.injective hh)

def puncturedDiskHomeomorph
    (e : closedBall (0:ℂ) 1 ≃ₜ closedBall (0:ℂ) 1)
    (h1 : e ⟨1,by norm_num⟩=⟨1,by norm_num⟩) :
    {w : ℂ // ‖w‖ ≤ 1 ∧ w ≠ 1} ≃ₜ {w : ℂ // ‖w‖ ≤ 1 ∧ w ≠ 1} := by
  let lift (w : {w : ℂ // ‖w‖ ≤ 1 ∧ w ≠ 1}) : closedBall (0:ℂ) 1 :=
    ⟨w,by simpa only [mem_closedBall,dist_zero_right] using w.property.1⟩
  have hlift : Continuous lift := continuous_subtype_val.subtype_mk _
  have h1i : e.symm ⟨1,by norm_num⟩=⟨1,by norm_num⟩ := by
    have hh := congrArg e.symm h1
    rw [e.symm_apply_apply] at hh
    exact hh.symm
  let f (w : {w : ℂ // ‖w‖ ≤ 1 ∧ w ≠ 1}) : ℂ := e (lift w)
  let g (w : {w : ℂ // ‖w‖ ≤ 1 ∧ w ≠ 1}) : ℂ := e.symm (lift w)
  have hf (w : {w : ℂ // ‖w‖ ≤ 1 ∧ w ≠ 1}) : ‖f w‖ ≤ 1 ∧ f w ≠ 1 := by
    refine ⟨?_,closedDisk_map_ne_one e h1 (lift w) w.property.2⟩
    simpa only [mem_closedBall,dist_zero_right] using (e (lift w)).property
  have hg (w : {w : ℂ // ‖w‖ ≤ 1 ∧ w ≠ 1}) : ‖g w‖ ≤ 1 ∧ g w ≠ 1 := by
    refine ⟨?_,closedDisk_map_ne_one e.symm h1i (lift w) w.property.2⟩
    simpa only [mem_closedBall,dist_zero_right] using (e.symm (lift w)).property
  exact
    { toFun := fun w => ⟨f w,hf w⟩
      invFun := fun w => ⟨g w,hg w⟩
      left_inv := fun w => by
        apply Subtype.ext
        exact congrArg (fun z : closedBall (0:ℂ) 1 => (z:ℂ)) (e.symm_apply_apply (lift w))
      right_inv := fun w => by
        apply Subtype.ext
        exact congrArg (fun z : closedBall (0:ℂ) 1 => (z:ℂ)) (e.apply_symm_apply (lift w))
      continuous_toFun := (continuous_subtype_val.comp (e.continuous.comp hlift)).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp (e.symm.continuous.comp hlift)).subtype_mk _ }

end SLEExactGauge

end

end OAI
