import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightBasisTrace

namespace OAI

/-! # Generalized weight spaces in a homogeneous word basis -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Set
open scoped BigOperators

variable {H M J : Type*} [LieRing H] [LieAlgebra ℝ H] [LieRing.IsNilpotent H]
  [AddCommGroup M] [Module ℝ M] [LieRingModule H M] [LieModule ℝ H M]
  [Fintype J]

/-- In a basis of generalized weight vectors, any chosen collection of
weight spaces lies in the span of the basis vectors with those weights. -/
theorem genWeightSpace_le_span_basis_by_weight
    (b : Basis J ℝ M) (χ : J → Weight ℝ H M)
    (hb : ∀ j, b j ∈ genWeightSpace M (χ j))
    (selected : Weight ℝ H M → Prop) (α : Weight ℝ H M) (hα : selected α) :
    (genWeightSpace M α).toSubmodule ≤ Submodule.span ℝ (b '' {j | selected (χ j)}) := by
  classical
  let S : Weight ℝ H M → Submodule ℝ M := fun β => (genWeightSpace M β).toSubmodule
  have hsp : iSup S = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Submodule.mem_iSup_of_mem (χ j) (hb j)
  have hind : iSupIndep S :=
    LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace' ℝ H M)
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsp
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap S) hds
  let A := fun β : Weight ℝ H M => if selected β then (S β).subtype else 0
  let D : M →ₗ[ℝ] M :=
    (DirectSum.toModule ℝ (Weight ℝ H M) M A).comp e.symm.toLinearMap
  have hD (β : Weight ℝ H M) (x : M) (hx : x ∈ S β) :
      D x = if selected β then x else 0 := by
    have he : e (DirectSum.lof ℝ (Weight ℝ H M) (fun β => S β) β ⟨x, hx⟩) = x :=
      DirectSum.coeLinearMap_lof S β ⟨x, hx⟩
    change (DirectSum.toModule ℝ (Weight ℝ H M) M A) (e.symm x) = _
    rw [← he, e.symm_apply_apply, DirectSum.toModule_lof]
    rw [he]
    by_cases hβ : selected β <;> simp only [A, hβ, ite_true, ite_false, LinearMap.zero_apply]
    rfl
  let P := Submodule.span ℝ (b '' {j | selected (χ j)})
  have hrange (y : M) : D y ∈ P := by
    rw [← b.sum_repr y, map_sum]
    apply Submodule.sum_mem
    intro j _
    rw [map_smul, hD (χ j) (b j) (hb j)]
    by_cases hj : selected (χ j)
    · rw [ite_eq_left hj]
      exact P.smul_mem _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · simp only [hj, ite_false, smul_zero]
      exact P.zero_mem
  intro x hx
  have he : D x = x := by rw [hD α x hx, ite_eq_left hα]
  exact he ▸ hrange x

end PolycyclicRecognition

end

end OAI
