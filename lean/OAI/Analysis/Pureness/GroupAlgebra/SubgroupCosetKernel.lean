import OAI.Analysis.Pureness.GroupAlgebra.ReducedGroupMatrixCoefficients
import Mathlib.GroupTheory.Coset.Defs

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped Classical
local instance subgroupCosetKernelDecidableEq {X : Type*} : DecidableEq X :=
  Classical.decEq X
open scoped InnerProductSpace
variable {G : Type*} [Group G]

def subgroupCosetVector (U : Subgroup G) (g : G) : GroupL2 (G ⧸ U) :=
  lp.single 2 (QuotientGroup.mk g⁻¹) 1

lemma subgroupCosetVector_norm (U : Subgroup G) (g : G) :
    ‖subgroupCosetVector U g‖ = 1 := by
  simp [subgroupCosetVector, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

lemma subgroupCosetVector_inner (U : Subgroup G) (g h : G) :
    ⟪subgroupCosetVector U g, subgroupCosetVector U h⟫_ℂ =
      if g*h⁻¹ ∈ U then 1 else 0 := by
  have hq : (QuotientGroup.mk g⁻¹ : G ⧸ U) = QuotientGroup.mk h⁻¹ ↔ g*h⁻¹ ∈ U := by
    simpa only [inv_inv] using (QuotientGroup.eq (s := U) (a := g⁻¹) (b := h⁻¹))
  rw [← hq]
  simp [subgroupCosetVector, lp.inner_single_left, lp.single_apply, Pi.single_apply]
end CuntzPureness

end

end OAI
