import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CStarAlgebras.ConnectedStageReduction
import OAI.Analysis.JiangSu.DimensionDrop.Matching
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropSquareTransfer
import OAI.Analysis.JiangSu.TensorProducts.StarTensorMap
import OAI.Analysis.JiangSu.Absorption.ConnectedUnitaryLift

namespace OAI

section

noncomputable section
namespace OriginalJiangSu
open JiangSuConstruction
open Pureness CStarAbsorption
open scoped CStarAlgebra TensorProduct

variable {T : Type*} [CStarAlgebra T]
variable (f : Algebra ⊗[ℂ] Algebra →⋆ₐ[ℂ] T)

theorem connected_half_flip (hf : Function.Injective f) :
    ConnectedApproximateInnerHalfFlip f := by
  classical
  apply system.connected_conjugacy_of_finiteStages (tensorLeft f) (tensorRight f)
  intro n F ε hε
  obtain ⟨k,W,hWd,hW⟩ := stage_matching n F
    (div_pos hε (by norm_num : (0:ℝ)<42))
  let i := system.inclusion (n+k)
  let g := f.comp (starTensorMap i i)
  have hg : Function.Injective g := hf.comp
    (starTensorMap_injective i i (system.inclusion_isometry (n+k)).injective
      (system.inclusion_isometry (n+k)).injective)
  let : NeZero (pair (n+k)).p := ⟨by have := (pair (n+k)).p_gt; omega⟩
  let : NeZero (pair (n+k)).q := ⟨by have := (pair (n+k)).q_gt; omega⟩
  obtain ⟨u,huj,hu⟩ := tensor_connected_half_flip_of_matching g hg
    (F.image (system.map (Nat.le_add_right n k))) hε W hWd (by
      intro x hx s t
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact hW y hy s t)
  refine ⟨u,huj,?_⟩
  intro x hx
  have h := hu _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
  simpa only [g,i,StarAlgHom.comp_apply,starTensorMap_tmul,map_one,
    system.inclusion_compatible,tensorLeft_apply,tensorRight_apply] using h

end OriginalJiangSu

end
end

end OAI
