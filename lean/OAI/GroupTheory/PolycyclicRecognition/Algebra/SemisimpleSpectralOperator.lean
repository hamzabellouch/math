import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace OAI

/-! # Scalar functional calculus on the eigenspaces of a semisimple operator

Only the finite-dimensional application needed for a matrix logarithm is
used. The operator is constructed from the internal eigenspace direct sum.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped DirectSum
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

def semisimpleEigenspaceEquiv (S : Module.End ℂ V) (hS : S.IsSemisimple) :
    (⨁ μ : ℂ, S.eigenspace μ) ≃ₗ[ℂ] V := by
  classical
  exact LinearEquiv.ofBijective (DirectSum.coeLinearMap S.eigenspace)
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      S.eigenspaces_iSupIndep hS.iSup_eigenspace_eq_top)

def semisimpleSpectralOperator (S : Module.End ℂ V) (hS : S.IsSemisimple)
    (f : ℂ → ℂ) : Module.End ℂ V := by
  classical
  exact (DirectSum.toModule ℂ ℂ V (fun μ => f μ • (S.eigenspace μ).subtype)).comp
    (semisimpleEigenspaceEquiv S hS).symm.toLinearMap

theorem semisimpleSpectralOperator_apply (S : Module.End ℂ V) (hS : S.IsSemisimple)
    (f : ℂ → ℂ) {μ : ℂ} {x : V} (hx : x ∈ S.eigenspace μ) :
    semisimpleSpectralOperator S hS f x = f μ • x := by
  classical
  have he : semisimpleEigenspaceEquiv S hS
      (DirectSum.lof ℂ ℂ (fun μ => S.eigenspace μ) μ ⟨x, hx⟩) = x :=
    DirectSum.coeLinearMap_lof S.eigenspace μ ⟨x, hx⟩
  change (DirectSum.toModule ℂ ℂ V (fun μ => f μ • (S.eigenspace μ).subtype))
    ((semisimpleEigenspaceEquiv S hS).symm x) = _
  rw [← he, LinearEquiv.symm_apply_apply, DirectSum.toModule_lof]
  rw [he]
  rfl

theorem semisimple_eigenspace_ext (S : Module.End ℂ V) (hS : S.IsSemisimple)
    {W : Type*} [AddCommGroup W] [Module ℂ W] {F G : V →ₗ[ℂ] W}
    (h : ∀ μ x, x ∈ S.eigenspace μ → F x = G x) : F = G := by
  apply sub_eq_zero.mp
  apply LinearMap.ker_eq_top.mp
  apply top_unique
  rw [← hS.iSup_eigenspace_eq_top]
  apply iSup_le
  intro μ x hx
  rw [LinearMap.mem_ker, LinearMap.sub_apply, h μ x hx, sub_self]

theorem semisimpleSpectralOperator_mul (S : Module.End ℂ V) (hS : S.IsSemisimple)
    (f g : ℂ → ℂ) :
    semisimpleSpectralOperator S hS (fun μ => f μ * g μ) =
      semisimpleSpectralOperator S hS f * semisimpleSpectralOperator S hS g := by
  apply semisimple_eigenspace_ext S hS
  intro μ x hx
  change _ = semisimpleSpectralOperator S hS f (semisimpleSpectralOperator S hS g x)
  rw [semisimpleSpectralOperator_apply S hS _ hx,
    semisimpleSpectralOperator_apply S hS _ hx, map_smul,
    semisimpleSpectralOperator_apply S hS _ hx, smul_smul, mul_comm]

theorem semisimpleSpectralOperator_commute (S : Module.End ℂ V) (hS : S.IsSemisimple)
    (f : ℂ → ℂ) (T : Module.End ℂ V) (hT : Commute S T) :
    Commute (semisimpleSpectralOperator S hS f) T := by
  change semisimpleSpectralOperator S hS f * T = T * semisimpleSpectralOperator S hS f
  apply semisimple_eigenspace_ext S hS
  intro μ x hx
  have hTx : T x ∈ S.eigenspace μ := by
    rw [Module.End.mem_eigenspace_iff]
    change (S * T) x = μ • T x
    rw [hT.eq]
    change T (S x) = μ • T x
    rw [Module.End.mem_eigenspace_iff.mp hx, map_smul]
  change semisimpleSpectralOperator S hS f (T x) = T (semisimpleSpectralOperator S hS f x)
  rw [semisimpleSpectralOperator_apply S hS _ hTx,
    semisimpleSpectralOperator_apply S hS _ hx, map_smul]

end PolycyclicRecognition

end

end OAI
