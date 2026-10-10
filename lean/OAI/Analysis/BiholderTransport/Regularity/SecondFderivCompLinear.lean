import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.HessianSmooth

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma second_fderiv_comp_linear_zero {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℝ} (hf : ContDiffAt ℝ 2 f 0) (L : E →L[ℝ] F) (v : E) :
    fderiv ℝ (fderiv ℝ (fun h => f (L h))) 0 v v =
      fderiv ℝ (fderiv ℝ f) 0 (L v) (L v) := by
  have hcomp : ContDiffAt ℝ 2 (fun h => f (L h)) 0 :=
    (show ContDiffAt ℝ 2 f (L 0) by simpa using hf).comp 0 L.contDiff.contDiffAt
  rw [← iteratedDeriv_two_affine_line hcomp v, ← iteratedDeriv_two_affine_line hf (L v)]
  congr 2
  ext t
  simp only [map_smul,zero_add]

end WeakMTWTransport
end

end OAI
