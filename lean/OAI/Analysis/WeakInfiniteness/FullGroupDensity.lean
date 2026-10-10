import Mathlib
import OAI.Analysis.WeakInfiniteness.FullGroupAlgebra

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal

namespace WeakPureInfiniteness

universe u

section GroupPolynomialDensity

variable {G : Type u} [Group G]

def groupSpan : StarSubalgebra ℂ (FullGroupAmbient G) where
  carrier := Submodule.span ℂ (Set.range (fullGroupOperator (G := G)))
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one, ← fullGroupOperator_one]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_range_self 1))
  mul_mem' {a} {b} hx hy := by
    change a * b ∈ Submodule.span ℂ (Set.range (fullGroupOperator (G := G)))
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨h, rfl⟩ := hy
        rw [← fullGroupOperator_mul]
        exact Submodule.subset_span (Set.mem_range_self (g*h))
      | zero => simp
      | add x y hx hy hpx hpy => rw [mul_add]; exact Submodule.add_mem _ hpx hpy
      | smul c x hx hpx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hpx
    | zero => simp
    | add x y hx hy hpx hpy => rw [add_mul]; exact Submodule.add_mem _ hpx hpy
    | smul c x hx hpx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hpx
  star_mem' {a} hx := by
    change star a ∈ Submodule.span ℂ (Set.range (fullGroupOperator (G := G)))
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g,rfl⟩ := hx
      rw [← fullGroupOperator_inv]
      exact Submodule.subset_span (Set.mem_range_self g⁻¹)
    | zero => simp
    | add x y hx hy hpx hpy => rw [star_add]; exact Submodule.add_mem _ hpx hpy
    | smul c x hx hpx => rw [star_smul]; exact Submodule.smul_mem _ (star c) hpx

lemma groupSpan_eq_adjoin : groupSpan (G := G) =
    StarAlgebra.adjoin ℂ (Set.range (fullGroupOperator (G := G))) := by
  apply le_antisymm
  · change Submodule.span ℂ (Set.range (fullGroupOperator (G := G))) ≤
      (StarAlgebra.adjoin ℂ (Set.range (fullGroupOperator (G := G)))).toSubalgebra.toSubmodule
    exact Submodule.span_le.mpr (StarAlgebra.subset_adjoin ℂ _)
  · exact StarAlgebra.adjoin_le (fun _ hx => Submodule.subset_span hx)

lemma fullGroupSubalgebra_eq_closure_span :
    (fullGroupSubalgebra G : Set (FullGroupAmbient G)) =
      closure (Submodule.span ℂ (Set.range (fullGroupOperator (G := G))) : Set (FullGroupAmbient G)) := by
  rw [fullGroupSubalgebra, closedStarSpan, ← groupSpan_eq_adjoin]
  rfl

end GroupPolynomialDensity

end WeakPureInfiniteness
end

end OAI
