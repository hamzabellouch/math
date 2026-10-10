import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Basic.Real.Basic
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section
namespace Zarankiewicz
open Module Submodule
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

def graphKernelEquiv (f g : V →ₗ[ℝ] W) :
    LinearMap.ker (f-g) ≃ₗ[ℝ] ↥(f.graph ⊓ g.graph) where
  toFun v := ⟨(v.val, f v.val), rfl, (sub_eq_zero.mp v.property)⟩
  invFun z := ⟨z.val.1, by
    change f z.val.1 - g z.val.1 = 0
    rw [← z.property.1, ← z.property.2, sub_self]⟩
  left_inv v := Subtype.ext rfl
  right_inv z := Subtype.ext (Prod.ext rfl z.property.1.symm)
  map_add' v w := Subtype.ext (Prod.ext rfl (f.map_add v.val w.val))
  map_smul' c v := Subtype.ext (Prod.ext rfl (f.map_smul c v.val))

theorem matrix_graph_finrank_add_rank (d : ℕ) (X Y : Matrix (Fin d) (Fin d) ℝ) :
    finrank ℝ ↥(X.mulVecLin.graph ⊓ Y.mulVecLin.graph) + (X-Y).rank = d := by
  have hdiff : X.mulVecLin - Y.mulVecLin = (X-Y).mulVecLin :=
    (map_sub (Matrix.mulVecBilin ℝ ℝ) X Y).symm
  have he := (graphKernelEquiv X.mulVecLin Y.mulVecLin).finrank_eq
  rw [hdiff] at he
  have hr := (X-Y).mulVecLin.finrank_range_add_finrank_ker
  change (X-Y).rank + finrank ℝ (LinearMap.ker (X-Y).mulVecLin) = finrank ℝ (Fin d → ℝ) at hr
  rw [he, Module.finrank_pi, Fintype.card_fin] at hr
  omega

theorem matrix_graph_disjoint (d : ℕ) (X Y : Matrix (Fin d) (Fin d) ℝ) (h : IsUnit (X-Y)) :
    Disjoint X.mulVecLin.graph Y.mulVecLin.graph := by
  apply disjoint_iff.mpr
  apply Submodule.finrank_eq_zero.mp
  have hh := matrix_graph_finrank_add_rank d X Y
  have hr := Matrix.rank_of_isUnit (X-Y) h
  simp only [Fintype.card_fin] at hr
  omega

end Zarankiewicz

end

end OAI
