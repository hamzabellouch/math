import OAI.Analysis.Pureness.GroupAlgebra.GroupRegularRepresentation
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Analysis.CStarAlgebra.Hom

namespace OAI
noncomputable section
namespace CuntzPureness
local instance reducedGroupCStarAlgebraDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
open scoped lp InnerProductSpace
variable (G : Type*) [Group G]

def groupRegularSpan : StarSubalgebra ℂ (GroupOperator G) where
  carrier := Submodule.span ℂ (Set.range (groupLeft (G := G)))
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  one_mem' := by
    simpa using (Submodule.subset_span (R := ℂ) (s := Set.range (groupLeft (G := G))) ⟨1,rfl⟩)
  mul_mem' := by
    intro a b ha hb
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g,rfl⟩ := hx
      induction hb using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨h,rfl⟩ := hy
        rw [← groupLeft_mul]
        exact Submodule.subset_span ⟨g*h,rfl⟩
      | zero => simp
      | add x y _ _ hx hy => simpa [mul_add] using Submodule.add_mem _ hx hy
      | smul c x _ hx => simpa [mul_smul_comm] using Submodule.smul_mem _ c hx
    | zero => simp
    | add x y _ _ hx hy => simpa [add_mul] using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa [smul_mul_assoc] using Submodule.smul_mem _ c hx
  algebraMap_mem' c := by
    have h : (1 : GroupOperator G) ∈ Submodule.span ℂ (Set.range (groupLeft (G := G))) := by
      simpa using (Submodule.subset_span (R := ℂ) (s := Set.range (groupLeft (G := G))) ⟨1,rfl⟩)
    simpa [Algebra.algebraMap_eq_smul_one] using Submodule.smul_mem _ c h
  star_mem' := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g,rfl⟩ := hx
      rw [groupLeft_star]
      exact Submodule.subset_span ⟨g⁻¹,rfl⟩
    | zero => simp
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa using Submodule.smul_mem _ (star c) hx

def reducedGroupAlgebra : StarSubalgebra ℂ (GroupOperator G) :=
  (groupRegularSpan G).topologicalClosure

instance reducedGroupAlgebra_closed : IsClosed (reducedGroupAlgebra G : Set (GroupOperator G)) :=
  StarSubalgebra.isClosed_topologicalClosure _
instance reducedGroupAlgebra_cstar : CStarAlgebra (reducedGroupAlgebra G) :=
  StarSubalgebra.cstarAlgebra _

lemma groupLeft_mem_reduced (g : G) : groupLeft g ∈ reducedGroupAlgebra G :=
  StarSubalgebra.le_topologicalClosure _ (Submodule.subset_span ⟨g,rfl⟩)

def reducedGroupUnitary : G →* unitary (reducedGroupAlgebra G) where
  toFun g := ⟨⟨groupLeft g,groupLeft_mem_reduced G g⟩, by
    constructor
    · exact Subtype.ext (Unitary.coe_star_mul_self (groupLeftUnitary g))
    · exact Subtype.ext (Unitary.coe_mul_star_self (groupLeftUnitary g))⟩
  map_one' := Subtype.ext (Subtype.ext groupLeft_one)
  map_mul' g h := Subtype.ext (Subtype.ext (groupLeft_mul g h))

lemma groupRegularSpan_eq_adjoin : groupRegularSpan G =
    StarAlgebra.adjoin ℂ (Set.range (groupLeft (G := G))) := by
  apply le_antisymm
  · change Submodule.span ℂ (Set.range (groupLeft (G := G))) ≤
      (StarAlgebra.adjoin ℂ (Set.range (groupLeft (G := G)))).toSubalgebra.toSubmodule
    exact Submodule.span_le.mpr (fun _ h => StarAlgebra.subset_adjoin ℂ _ h)
  · exact StarAlgebra.adjoin_le (fun _ h => Submodule.subset_span h)

lemma reducedGroupAlgebra_eq_generated : reducedGroupAlgebra G =
    (StarAlgebra.adjoin ℂ (Set.range (groupLeft (G := G)))).topologicalClosure := by
  rw [reducedGroupAlgebra, groupRegularSpan_eq_adjoin]

lemma reducedGroup_commute_right (a : reducedGroupAlgebra G) (g : G) :
    Commute (a : GroupOperator G) (groupRight g) := by
  have hc : IsClosed {a : GroupOperator G | Commute a (groupRight g)} :=
    isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  apply closure_minimal (t := {a : GroupOperator G | Commute a (groupRight g)}) ?_ hc a.property
  intro x hx
  change x ∈ Submodule.span ℂ (Set.range (groupLeft (G := G))) at hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨h,rfl⟩ := hx; exact groupLeft_commute_right h g
  | zero => exact Commute.zero_left _
  | add x y _ _ hx hy => exact hx.add_left hy
  | smul c x _ hx => exact hx.smul_left c

theorem reducedGroup_vacuum_separating (a : reducedGroupAlgebra G)
    (ha : (a : GroupOperator G) groupVacuum = 0) : a = 0 := by
  apply Subtype.ext
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro g
  apply ContinuousLinearMap.ext
  intro c
  change (a : GroupOperator G) (lp.single 2 g c) = 0
  have hone : (a : GroupOperator G) (lp.single 2 g 1) = 0 := by
    rw [← inv_inv g, ← groupRight_vacuum]
    have h := congrArg (fun T : GroupOperator G => T groupVacuum)
      (reducedGroup_commute_right G a g⁻¹).eq
    simpa [mul_apply_eq_comp, ha] using h
  have he : lp.single (E := fun _ : G => ℂ) 2 g c = c • lp.single 2 g 1 := by
    simpa using lp.single_smul (E := fun _ : G => ℂ) 2 g c (1 : ℂ)
  rw [he, map_smul, hone, smul_zero]
end CuntzPureness

end

end OAI
