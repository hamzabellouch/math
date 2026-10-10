import Mathlib
import OAI.Analysis.MatrixSigning.Calculus.JetBound

namespace OAI

open Matrix

namespace CurrentKS.Calculus
noncomputable section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

local instance : NormedAddCommGroup (G →L[ℝ] F) := inferInstance
local instance : NormedSpace ℝ (G →L[ℝ] F) := inferInstance
local instance : NormedAddCommGroup ((G →L[ℝ] F) →L[ℝ] F) := inferInstance
local instance : NormedSpace ℝ ((G →L[ℝ] F) →L[ℝ] F) := inferInstance
local instance : NormedAddCommGroup (F →L[ℝ] G) := inferInstance
local instance : NormedSpace ℝ (F →L[ℝ] G) := inferInstance
local instance : NormedAddCommGroup ((F →L[ℝ] G) →L[ℝ] G) := inferInstance
local instance : NormedSpace ℝ ((F →L[ℝ] G) →L[ℝ] G) := inferInstance

lemma norm_smulRight_id_le (v : F) :
    ‖(ContinuousLinearMap.id ℝ ℝ).smulRight v‖ ≤ ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v)
  intro r
  change ‖r • v‖ ≤ ‖v‖*‖r‖
  rw [norm_smul,mul_comm]

lemma JetBound.smul_const {f : E → ℝ} {x : E} {B C : ℝ} (v : F)
    (hf : ContDiffAt ℝ 3 f x) (hB : JetBound f x B) (hC : ‖v‖ ≤ C) :
    JetBound (fun y => f y • v) x (C*B) := by
  exact hB.linear_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight v) hf
    ((norm_smulRight_id_le v).trans hC)

lemma norm_apply_bilinear_le : ‖ContinuousLinearMap.apply ℝ F (E := G)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro L
  change ‖L v‖ ≤ (1*‖v‖)*‖L‖
  simpa only [one_mul,mul_one,mul_comm] using L.le_opNorm v

lemma JetBound.apply {f : E → F →L[ℝ] G} {g : E → F} {x : E} {B C : ℝ}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x)
    (hB : JetBound f x B) (hC : JetBound g x C) :
    JetBound (fun y => f y (g y)) x (8*C*B) := by
  exact JetBound.bilinear (E := E) (F := F) (G := F →L[ℝ] G) (H := G)
    (ContinuousLinearMap.apply ℝ G (E := F)) hg hf hC hB
    (norm_apply_bilinear_le (F := G) (G := F))

lemma norm_comp_contractions (L : F →L[ℝ] G) (T : E →L[ℝ] F)
    (hL : ‖L‖ ≤ 1) (hT : ‖T‖ ≤ 1) : ‖L.comp T‖ ≤ 1 :=
  (ContinuousLinearMap.opNorm_comp_le L T).trans
    (by simpa only [one_mul] using mul_le_mul hL hT (norm_nonneg T) zero_le_one)

end
end CurrentKS.Calculus

end OAI
