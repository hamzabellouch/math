import Mathlib.Algebra.Lie.Weights.Linear
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Basic.Real.Basic

namespace OAI

/-! # Trace in an arbitrary generalized-weight basis

Bracket-word bases need not triangularize the nilpotent parts of the Cartan
action. The trace is nevertheless the sum of their weights. We prove this by
separating the scalar action on each generalized weight space; the residual
operator has zero trace on every such space.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped BigOperators

variable {H M J : Type*} [LieRing H] [LieAlgebra ℝ H] [LieRing.IsNilpotent H]
  [AddCommGroup M] [Module ℝ M] [LieRingModule H M] [LieModule ℝ H M]
  [FiniteDimensional ℝ M] [Fintype J]

theorem trace_eq_sum_of_generalizedWeight_basis
    (b : Basis J ℝ M) (χ : J → Weight ℝ H M)
    (hb : ∀ j, b j ∈ genWeightSpace M (χ j)) (h : H) :
    LinearMap.trace ℝ M (toEnd ℝ H M h) = ∑ j, χ j h := by
  classical
  let S : Weight ℝ H M → Submodule ℝ M := fun α => (genWeightSpace M α).toSubmodule
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
  let D : M →ₗ[ℝ] M := (DirectSum.toModule ℝ (Weight ℝ H M) M
    (fun α => (α h) • (S α).subtype)).comp e.symm.toLinearMap
  have hD (α : Weight ℝ H M) (x : M) (hx : x ∈ S α) : D x = α h • x := by
    have he : e (DirectSum.lof ℝ (Weight ℝ H M) (fun α => S α) α ⟨x, hx⟩) = x :=
      DirectSum.coeLinearMap_lof S α ⟨x, hx⟩
    change (DirectSum.toModule ℝ (Weight ℝ H M) M
      (fun α => (α h) • (S α).subtype)) (e.symm x) = _
    rw [← he, e.symm_apply_apply, DirectSum.toModule_lof]
    rw [he]
    rfl
  let f := toEnd ℝ H M h
  have hstable (α : Weight ℝ H M) : Set.MapsTo (f - D) (S α) (S α) := by
    intro x hx
    change f x - D x ∈ S α
    rw [hD α x hx]
    exact (genWeightSpace M α).sub_mem ((genWeightSpace M α).lie_mem hx)
      ((genWeightSpace M α).smul_mem _ hx)
  have htrace : LinearMap.trace ℝ M (f - D) = 0 := by
    rw [LinearMap.trace_eq_sum_trace_restrict hds hstable]
    apply Finset.sum_eq_zero
    intro α _
    have hr : (f - D).restrict (hstable α) =
        toEnd ℝ H (genWeightSpace M α) h - (α h) • LinearMap.id := by
      ext x
      change f x - D x = f x - α h • (x : M)
      rw [hD α x x.property]
    rw [hr, map_sub, map_smul, LinearMap.trace_id]
    change LinearMap.trace ℝ (genWeightSpace M α)
      (toEnd ℝ H (genWeightSpace M α) h) -
        α h • (Module.finrank ℝ (genWeightSpace M α) : ℝ) = 0
    rw [trace_toEnd_genWeightSpace]
    simp only [nsmul_eq_mul, smul_eq_mul, mul_comm, sub_self]
  have hDtrace : LinearMap.trace ℝ M D = ∑ j, χ j h := by
    rw [LinearMap.trace_eq_matrix_trace ℝ b]
    simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [hD (χ j) (b j) (hb j)]
    simp
  rw [map_sub, sub_eq_zero] at htrace
  exact htrace.trans hDtrace

end PolycyclicRecognition

end

end OAI
