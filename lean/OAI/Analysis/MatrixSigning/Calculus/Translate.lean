import Mathlib
import OAI.Analysis.MatrixSigning.Calculus.JetBound

namespace OAI

open Matrix

namespace CurrentKS.Calculus
noncomputable section
open scoped ContDiff

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma JetBound.translate {f : E → F} {x a : E} {B : ℝ}
    (h : JetBound f (a+x) B) : JetBound (fun y => f (a+y)) x B := by
  intro n hn
  rw [iteratedFDeriv_comp_add_left]
  exact h n hn

lemma norm_lineMap_le_one (h : E) (hh : ‖h‖ ≤ 1) :
    ‖(ContinuousLinearMap.id ℝ ℝ).smulRight h‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro r
  change ‖r • h‖ ≤ 1*‖r‖
  rw [norm_smul]
  nlinarith [norm_nonneg r]

lemma contDiffAt_translated_zero {f : E → F} {x : E}
    (hf : ContDiffAt ℝ 3 f x) : ContDiffAt ℝ 3 (fun y => f (x+y)) (0:E) := by
  have H : ContDiffAt ℝ 3 f (x+0) := by simpa only [add_zero] using hf
  exact H.comp 0 (contDiffAt_const.add contDiffAt_id)

lemma JetBound.line {f : E → F} {x h : E} {B : ℝ}
    (hf : ContDiffAt ℝ 3 f x) (hB : JetBound f x B) (hh : ‖h‖ ≤ 1) :
    JetBound (fun t : ℝ => f (x+t • h)) 0 B := by
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight h
  have h0 : JetBound (fun y => f (x+y)) (0:E) B := by
    exact JetBound.translate (by simpa only [add_zero] using hB)
  have hf0 := contDiffAt_translated_zero hf
  have ht := JetBound.comp_linear (E:=ℝ) (F:=E) (G:=F) (x:=0) L
    (show ContDiffAt ℝ 3 (fun y => f (x+y)) (L 0) by simpa only [map_zero] using hf0)
    (show JetBound (fun y => f (x+y)) (L 0) B by simpa only [map_zero] using h0)
    (norm_lineMap_le_one h hh)
  exact ht

end
end CurrentKS.Calculus

end OAI
