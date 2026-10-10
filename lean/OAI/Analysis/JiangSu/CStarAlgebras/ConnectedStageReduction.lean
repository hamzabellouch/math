import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropSquareTransfer

namespace OAI

section

noncomputable section
namespace SequentialCStar.System
open scoped CStarAlgebra

variable {C : ℕ → Type*} [∀ n,CStarAlgebra (C n)] [∀ n,Nontrivial (C n)]
variable (S : System C)
variable {T : Type*} [CStarAlgebra T]
variable (ι κ : S.Limit →⋆ₐ[ℂ] T)

theorem connected_conjugacy_of_finiteStages
    (h : ∀ n : ℕ,∀ F : Finset (C n),∀ ε : ℝ,0<ε → ∃ u : unitary T,Joined 1 u ∧
      ∀ x∈F,‖(u:T)*ι (S.inclusion n x)*star (u:T)-κ (S.inclusion n x)‖<ε) :
    ∀ F : Finset S.Limit,∀ ε : ℝ,0<ε → ∃ u : unitary T,Joined 1 u ∧
      ∀ x∈F,‖(u:T)*ι x*star (u:T)-κ x‖<ε := by
  classical
  intro F ε hε
  obtain ⟨n,b,hb⟩ := S.finite_set_common_stage F (div_pos hε (by norm_num : (0:ℝ)<3))
  obtain ⟨u,huj,hu⟩ := h n (Finset.univ.image b) (ε/3) (by positivity)
  refine ⟨u,huj,?_⟩
  intro x hx
  let z : F := ⟨x,hx⟩
  let y := S.inclusion n (b z)
  have hxy : ‖x-y‖<ε/3 := hb z
  have hmid : ‖(u:T)*ι y*star (u:T)-κ y‖<ε/3 :=
    hu _ (Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩)
  have hleft : ‖(u:T)*ι x*star (u:T)-(u:T)*ι y*star (u:T)‖<ε/3 :=
    (S.conjugacy_difference_bound ι u x y).trans_lt hxy
  have hright : ‖κ y-κ x‖<ε/3 := by
    rw [←map_sub]
    exact (NonUnitalStarAlgHom.norm_apply_le κ (y-x)).trans_lt (by simpa only [norm_sub_rev] using hxy)
  have htri₁ := norm_sub_le_norm_sub_add_norm_sub
    ((u:T)*ι x*star (u:T)) ((u:T)*ι y*star (u:T)) (κ x)
  have htri₂ := norm_sub_le_norm_sub_add_norm_sub
    ((u:T)*ι y*star (u:T)) (κ y) (κ x)
  linarith

end SequentialCStar.System

end
end

end OAI
