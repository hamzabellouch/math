import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.CoreGeometry
import OAI.Combinatorics.RamseyFive.Marking.TwoScan

namespace OAI

namespace SharpRamseyFive.CoreGeometry
open Module ProjectiveIncidence Marking
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma bidual_rep_mem (x : ℙ K V) (W : Submodule K (Dual K (Dual K V))) :
    (bidualPoint x).rep∈W ↔ (Dual.eval K V x.rep)∈W := by
  change (bidualPoint x).rep∈W ↔ x.rep∈W.comap (Dual.eval K V)
  rw [rep_mem_iff,rep_mem_iff]
  induction x using Projectivization.ind with | h v hv =>
  change (Projectivization.map (Module.evalEquiv K V).toLinearMap
    (Module.evalEquiv K V).injective (Projectivization.mk K v hv)).submodule≤W ↔ _
  rw [Projectivization.map_mk,Projectivization.submodule_mk,
    Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem,
    Submodule.span_singleton_le_iff_mem]
  rfl

lemma inRectangle_swap (W : Submodule K (Dual K (Dual K V))) (f : FlagPair K V) :
    InRectangle W (swapFlag f).1.rep (swapFlag f).2.rep ↔
      InRectangle W.dualCoannihilator f.1.rep f.2.rep := by
  simp only [InRectangle,swapFlag_apply]
  rw [bidual_rep_mem]
  have he : (Dual.eval K V f.1.rep)∈W ↔ f.1.rep∈W.dualCoannihilator.dualCoannihilator := by
    conv_lhs => rw [←Subspace.dualCoannihilator_dualAnnihilator_eq (W:=W)]
    rfl
  rw [he,and_comm]

omit [FiniteDimensional K V] in
lemma occupancy_reindex {I J : Type} [Fintype I] [Fintype J]
    (x : I→FlagPair K V) (e : J→I) (he : Function.Injective e) (M : ℝ)
    (h : ∀W : Submodule K (Dual K V),
      (∑i,if InRectangle W (x i).1.rep (x i).2.rep then (1:ℝ) else 0)≤M) :
    ∀W : Submodule K (Dual K V),
      (∑j,if InRectangle W (x (e j)).1.rep (x (e j)).2.rep then (1:ℝ) else 0)≤M := by
  intro W
  apply le_trans _ (h W)
  calc
    _ = ∑i∈Finset.univ.image e,if InRectangle W (x i).1.rep (x i).2.rep then (1:ℝ) else 0 := by
      rw [Finset.sum_image (by intro a ha b hb hab;exact he hab)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
      intro i hi hni
      split <;> norm_num)

lemma occupancy_reverse {n : ℕ} (x : Fin n→FlagPair K V) (M : ℝ)
    (h : ∀W : Submodule K (Dual K V),
      (∑i,if InRectangle W (x i).1.rep (x i).2.rep then (1:ℝ) else 0)≤M) :
    ∀W : Submodule K (Dual K (Dual K V)),
      (∑i,if InRectangle W (reverseTuple x i).1.rep (reverseTuple x i).2.rep then (1:ℝ) else 0)≤M := by
  intro W
  simp only [reverseTuple,inRectangle_swap]
  exact occupancy_reindex x Fin.rev Fin.rev_injective M h W.dualCoannihilator
end
end SharpRamseyFive.CoreGeometry

end OAI
